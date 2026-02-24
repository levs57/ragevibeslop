use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup, VariableBaseMSM};
use ark_ff::{Field, One, Zero};
use ark_groth16::Groth16;
use ark_groth16::r1cs_to_qap::PvugcReduction;
use ark_groth16::VerifyingKey as Groth16VK;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_serialize::CanonicalSerialize;
use ark_snark::SNARK;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use std::collections::HashSet;

#[derive(Clone)]
struct WitnessBasesResult<Ep: Pairing> {
    h_query_wit: Vec<(u32, u32, Ep::G1Affine)>,
    omitted_gap_bases: Vec<(u32, u32, Ep::G1Affine)>,
}

#[derive(Clone)]
struct LeanProvingKey<Ep: Pairing> {
    vk: Groth16VK<Ep>,
    beta_g1: Ep::G1Affine,
    delta_g1: Ep::G1Affine,
    a_query_wit: Vec<Ep::G1Affine>,
    b_g1_query: Vec<Ep::G1Affine>,
    l_query: Vec<Ep::G1Affine>,
    h_query_wit: Vec<(u32, u32, Ep::G1Affine)>,
}

#[derive(Clone)]
struct MockCircuit {
    x_public: Vec<Fr>,
    y_private: Vec<Fr>,
    z_private: Fr,
}

impl ConstraintSynthesizer<Fr> for MockCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        use ark_relations::{lc, r1cs::Variable};
        let x_vars: Vec<_> = self
            .x_public
            .iter()
            .map(|x| cs.new_input_variable(|| Ok(*x)))
            .collect::<Result<_, _>>()?;
        let y_vars: Vec<_> = self
            .y_private
            .iter()
            .map(|y| cs.new_witness_variable(|| Ok(*y)))
            .collect::<Result<_, _>>()?;
        let z = cs.new_witness_variable(|| Ok(self.z_private))?;
        for (x, y) in x_vars.iter().zip(y_vars.iter()) {
            cs.enforce_constraint(lc!() + Variable::One, lc!() + *y, lc!() + *x)?;
        }
        cs.enforce_constraint(lc!() + z, lc!() + z, lc!() + y_vars[0])?;
        Ok(())
    }
}

fn serial_ifft_g1(a: &mut [<E as Pairing>::G1], domain: &GeneralEvaluationDomain<Fr>) {
    let n = a.len();
    let n_inv = Fr::from(n as u64).inverse().expect("domain size invertible");
    let input = a.to_vec();
    let mut out = vec![<E as Pairing>::G1::zero(); n];
    for (k, out_k) in out.iter_mut().enumerate() {
        let mut acc = <E as Pairing>::G1::zero();
        for (j, val) in input.iter().enumerate() {
            let idx = if j == 0 || k == 0 { 0 } else { (n - ((j * k) % n)) % n };
            acc += *val * domain.element(idx);
        }
        *out_k = acc * n_inv;
    }
    a.copy_from_slice(&out);
}

fn compute_witness_bases_from_pk(pk: &ark_groth16::ProvingKey<E>, circuit: MockCircuit) -> WitnessBasesResult<E> {
    use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal};
    let cs = ConstraintSystem::<Fr>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    circuit.generate_constraints(cs.clone()).expect("synthesis failed");
    cs.finalize();
    let matrices = cs.to_matrices().expect("matrix extraction failed");

    let num_constraints = cs.num_constraints();
    let num_inputs = cs.num_instance_variables();
    let qap_domain_size = num_constraints + num_inputs;
    let domain = GeneralEvaluationDomain::<Fr>::new(qap_domain_size)
        .or_else(|| GeneralEvaluationDomain::<Fr>::new(qap_domain_size.next_power_of_two()))
        .expect("domain creation failed");
    let domain_size = domain.size();

    let num_vars = cs.num_instance_variables() + cs.num_witness_variables();
    let mut col_a = vec![Vec::new(); num_vars];
    let mut col_b = vec![Vec::new(); num_vars];
    for (row, terms) in matrices.a.iter().enumerate() {
        if row < domain_size {
            for &(val, col) in terms {
                col_a[col].push((row, val));
            }
        }
    }
    for (row, terms) in matrices.b.iter().enumerate() {
        if row < domain_size {
            for &(val, col) in terms {
                col_b[col].push((row, val));
            }
        }
    }

    let mut h_query_proj: Vec<_> = pk.h_query.iter().map(|p| p.into_group()).collect();
    if h_query_proj.len() < domain_size {
        h_query_proj.resize(domain_size, <E as Pairing>::G1::zero());
    } else {
        h_query_proj.truncate(domain_size);
    }
    serial_ifft_g1(&mut h_query_proj, &domain);
    let lagrange_srs: Vec<_> = h_query_proj.into_iter().map(|p| p.into_affine()).collect();

    let num_pub = cs.num_instance_variables();
    let mut omit_const_wit_cols: HashSet<usize> = HashSet::new();
    if num_pub > 1 {
        for pub_col in 1..num_pub {
            let mut c_rows = Vec::new();
            for (row, terms) in matrices.c.iter().enumerate() {
                if row >= domain_size {
                    continue;
                }
                if terms.iter().any(|&(_, col)| col == pub_col) {
                    c_rows.push(row);
                }
            }
            for &row in &c_rows {
                let b_wit_cols: Vec<usize> = matrices.b[row]
                    .iter()
                    .filter_map(|&(_, col)| if col >= num_pub { Some(col) } else { None })
                    .collect();
                if b_wit_cols.len() == 1 {
                    omit_const_wit_cols.insert(b_wit_cols[0]);
                }
            }
        }
    }

    let mut vars_a = HashSet::new();
    let mut vars_b = HashSet::new();
    for (row, terms) in matrices.a.iter().enumerate() {
        if row < domain_size {
            for &(_, col) in terms {
                vars_a.insert(col);
            }
        }
    }
    for (row, terms) in matrices.b.iter().enumerate() {
        if row < domain_size {
            for &(_, col) in terms {
                vars_b.insert(col);
            }
        }
    }

    let mut active_pairs = HashSet::new();
    for &i in &vars_a {
        for &j in &vars_b {
            if i < num_pub && j < num_pub {
                continue;
            }
            if i == 0 && omit_const_wit_cols.contains(&j) {
                continue;
            }
            active_pairs.insert((i, j));
        }
    }

    let n_field = domain.size_as_field_element();
    let t0 = (n_field - Fr::one()) * (n_field + n_field).inverse().expect("2n invertible");
    let mut q_vector = Vec::with_capacity(domain_size);
    for k in 0..domain_size {
        let wk = domain.element(k);
        let mut acc = <E as Pairing>::G1::zero();
        for m in 0..domain_size {
            let coeff = if k == m {
                t0
            } else {
                (n_field * (wk - domain.element(m))).inverse().expect("non-zero denominator")
            };
            acc += lagrange_srs[m].into_group() * coeff;
        }
        q_vector.push(acc.into_affine());
    }

    let domain_elements: Vec<_> = (0..domain_size).map(|i| domain.element(i)).collect();
    let compute_pair = |i_idx: usize, j_idx: usize| -> Option<<E as Pairing>::G1Affine> {
        let rows_u: &Vec<(usize, Fr)> = &col_a[i_idx];
        let rows_v: &Vec<(usize, Fr)> = &col_b[j_idx];
        if rows_u.is_empty() || rows_v.is_empty() {
            return None;
        }
        let mut acc_u = vec![Fr::zero(); rows_u.len()];
        let mut acc_v = vec![Fr::zero(); rows_v.len()];
        let mut diag_terms: Vec<(usize, Fr)> = Vec::new();

        for (idx_u, &(_, val_u)) in rows_u.iter().enumerate() {
            for (idx_v, &(_, val_v)) in rows_v.iter().enumerate() {
                let k = rows_u[idx_u].0;
                let m = rows_v[idx_v].0;
                let prod = val_u * val_v;
                if k == m {
                    diag_terms.push((k, prod));
                } else {
                    let wk = domain_elements[k];
                    let wm = domain_elements[m];
                    let inv_denom = (n_field * (wk - wm)).inverse().expect("non-zero denominator");
                    let common = prod * inv_denom;
                    acc_u[idx_u] += common * wm;
                    acc_v[idx_v] -= common * wk;
                }
            }
        }

        let mut pair_bases = Vec::new();
        let mut pair_scalars = Vec::new();
        for (idx_u, &(k, _)) in rows_u.iter().enumerate() {
            if !acc_u[idx_u].is_zero() {
                pair_bases.push(lagrange_srs[k]);
                pair_scalars.push(acc_u[idx_u]);
            }
        }
        for (idx_v, &(m, _)) in rows_v.iter().enumerate() {
            if !acc_v[idx_v].is_zero() {
                pair_bases.push(lagrange_srs[m]);
                pair_scalars.push(acc_v[idx_v]);
            }
        }
        if !diag_terms.is_empty() {
            diag_terms.sort_unstable_by_key(|(k, _)| *k);
            let mut cur_k = diag_terms[0].0;
            let mut cur_acc = Fr::zero();
            for (k, s) in diag_terms.into_iter() {
                if k != cur_k {
                    if !cur_acc.is_zero() {
                        pair_bases.push(q_vector[cur_k]);
                        pair_scalars.push(cur_acc);
                    }
                    cur_k = k;
                    cur_acc = s;
                } else {
                    cur_acc += s;
                }
            }
            if !cur_acc.is_zero() {
                pair_bases.push(q_vector[cur_k]);
                pair_scalars.push(cur_acc);
            }
        }
        if pair_bases.is_empty() {
            return None;
        }
        let h_acc = <<E as Pairing>::G1 as VariableBaseMSM>::msm(&pair_bases, &pair_scalars).unwrap();
        if h_acc.is_zero() { None } else { Some(h_acc.into_affine()) }
    };

    let mut sorted_pairs: Vec<(usize, usize)> = active_pairs.into_iter().collect();
    sorted_pairs.sort();
    let mut h_wit = Vec::new();
    for (i, j) in sorted_pairs {
        if let Some(p) = compute_pair(i, j) {
            h_wit.push((i as u32, j as u32, p));
        }
    }

    let mut omitted_gap_bases = Vec::new();
    for &j in &omit_const_wit_cols {
        if let Some(p) = compute_pair(0usize, j) {
            omitted_gap_bases.push((0u32, j as u32, p));
        }
    }

    WitnessBasesResult { h_query_wit: h_wit, omitted_gap_bases }
}

fn audit_witness_bases(wb: &WitnessBasesResult<E>, num_public: usize) {
    for &(i, j, _) in &wb.h_query_wit {
        let i_idx = i as usize;
        let j_idx = j as usize;
        let pure_public = i_idx > 0 && i_idx < num_public && j_idx > 0 && j_idx < num_public;
        assert!(!pure_public, "h_query_wit leaked pure public pair ({}, {})", i, j);
        if i_idx > 0 && i_idx < num_public {
            panic!("[SECURITY AUDIT FAIL] Public input column {} found in Matrix A (via pair {}, {}). Public inputs must only appear in Matrix B (One-Sided Property).", i_idx, i, j);
        }
    }

    let mut const_const_count = 0usize;
    let mut pub_wit_count = 0usize;
    for &(i, j, _) in &wb.h_query_wit {
        let i_idx = i as usize;
        let j_idx = j as usize;
        if i_idx == 0 && j_idx == 0 {
            const_const_count += 1;
        } else if i_idx > 0 && i_idx < num_public && j_idx >= num_public {
            pub_wit_count += 1;
        }
    }
    assert_eq!(pub_wit_count, 0);
    assert_eq!(const_const_count, 0);
}

fn audit_gap_preimages_not_directly_published(lean_pk: &LeanProvingKey<E>, omitted_gap_bases: &[(u32, u32, <E as Pairing>::G1Affine)]) {
    fn key<Ep: Pairing>(p: &Ep::G1Affine) -> Vec<u8> {
        let mut out = Vec::new();
        p.serialize_compressed(&mut out).expect("G1 serialize_compressed");
        out
    }

    let mut published: HashSet<Vec<u8>> = HashSet::new();
    published.insert(key::<E>(&lean_pk.vk.alpha_g1));
    for g in &lean_pk.vk.gamma_abc_g1 { published.insert(key::<E>(g)); }
    published.insert(key::<E>(&lean_pk.beta_g1));
    published.insert(key::<E>(&lean_pk.delta_g1));
    for g in &lean_pk.a_query_wit { published.insert(key::<E>(g)); }
    for g in &lean_pk.b_g1_query { published.insert(key::<E>(g)); }
    for g in &lean_pk.l_query { published.insert(key::<E>(g)); }
    for &(_, _, g) in &lean_pk.h_query_wit { published.insert(key::<E>(&g)); }

    let offenders: Vec<(u32, u32)> = omitted_gap_bases
        .iter()
        .filter_map(|&(i, j, g)| if published.contains(&key::<E>(&g)) { Some((i, j)) } else { None })
        .take(8)
        .collect();
    assert!(offenders.is_empty(), "offenders: {:?}", offenders);
}

pub fn pvugc_setup_checks() {
    let mut rng = StdRng::seed_from_u64(0xA11CE);
    let circuit = MockCircuit {
        x_public: vec![Fr::from(5u64), Fr::from(11u64), Fr::from(13u64)],
        y_private: vec![Fr::from(5u64), Fr::from(11u64), Fr::from(13u64)],
        z_private: Fr::from(9u64),
    };
    let (pk, vk) = Groth16::<E, PvugcReduction>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let wb = compute_witness_bases_from_pk(&pk, circuit);

    assert!(!wb.omitted_gap_bases.is_empty());
    let num_pub = vk.gamma_abc_g1.len();
    audit_witness_bases(&wb, num_pub);

    let lean_pk = LeanProvingKey::<E> {
        vk: vk.clone(),
        beta_g1: pk.beta_g1,
        delta_g1: pk.delta_g1,
        a_query_wit: pk.a_query.clone(),
        b_g1_query: pk.b_g1_query.clone(),
        l_query: pk.l_query.clone(),
        h_query_wit: wb.h_query_wit.clone(),
    };
    audit_gap_preimages_not_directly_published(&lean_pk, &wb.omitted_gap_bases);
}
