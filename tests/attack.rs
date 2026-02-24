use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, One, PrimeField, Zero};
use ark_groth16::r1cs_to_qap::PvugcReduction;
use ark_groth16::{Groth16, VerifyingKey as Groth16VK};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_snark::SNARK;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_std::UniformRand;
use std::collections::{BTreeMap, HashSet};
#[path = "helpers/pvugc_setup_check.rs"]
mod pvugc_setup_check;
use symbolic_core::symbolic_attack::{
    build_constructible_elements, solve_target_from_constructible, ConstructibleKind,
    LaurentMonomial, LaurentPolynomial,
};
use symbolic_core::{
    arm_columns, build_column_bases, compute_baked_target, compute_r_to_rho, PvugcVk,
};

#[derive(Clone)]
struct MockCircuit {
    x_public: Vec<Fr>,
    y_private: Vec<Option<Fr>>,
    z_private: Option<Fr>,
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
            .x_public
            .iter()
            .enumerate()
            .map(|(i, _)| {
                let y = self
                    .y_private
                    .get(i)
                    .copied()
                    .flatten()
                    .unwrap_or_else(Fr::zero);
                cs.new_witness_variable(|| Ok(y))
            })
            .collect::<Result<_, _>>()?;
        let z_val = self.z_private.unwrap_or_else(Fr::zero);
        let z = cs.new_witness_variable(|| Ok(z_val))?;

        for (x, y) in x_vars.iter().zip(y_vars.iter()) {
            cs.enforce_constraint(lc!() + Variable::One, lc!() + *y, lc!() + *x)?;
        }
        cs.enforce_constraint(lc!() + z, lc!() + z, lc!() + y_vars[0])?;
        Ok(())
    }
}

#[derive(Clone)]
struct LeanProvingKey<Ep: Pairing> {
    vk: Groth16VK<Ep>,
    beta_g1: Ep::G1Affine,
    delta_g1: Ep::G1Affine,
    a_query_wit: Vec<Ep::G1Affine>,
    b_g1_query: Vec<Ep::G1Affine>,
    h_query_wit: Vec<(u32, u32, Ep::G1Affine)>,
    l_query: Vec<Ep::G1Affine>,
}

#[derive(Clone)]
struct SymbolicOracleData {
    h_query_wit_mono: Vec<(u32, u32, Vec<Fr>)>,
    omitted_gap_mono: Vec<(u32, u32, Vec<Fr>)>,
    omitted_gap_forms: Vec<(u32, u32, Vec<Fr>)>,
    a_mono: Vec<Vec<Fr>>,
    b_mono: Vec<Vec<Fr>>,
    c_mono: Vec<Vec<Fr>>,
}

#[derive(Clone)]
struct SetupArtifacts {
    lean_pk: LeanProvingKey<E>,
    vk: Groth16VK<E>,
    pvugc_vk: PvugcVk<E>,
    x_public: Vec<Fr>,
    col_arms: symbolic_core::ColumnArms<E>,
    oracle: SymbolicOracleData,
}


fn mono(s: &str) -> LaurentPolynomial<Fr> {
    LaurentPolynomial::monomial(Fr::one(), LaurentMonomial::from_symbol(s))
}

fn form_to_monomial_tau_poly(form: &[Fr]) -> LaurentPolynomial<Fr> {
    let mut p = LaurentPolynomial::<Fr>::zero();
    for (idx, coeff) in form.iter().copied().enumerate() {
        if coeff.is_zero() {
            continue;
        }
        p.add_term(coeff, LaurentMonomial::from_powers(&[("TAU", idx as i64)]));
    }
    p
}

fn to_lagrange_poly(form: &[Fr]) -> LaurentPolynomial<Fr> {
    form_to_monomial_tau_poly(form)
}

fn scale_poly(poly: &LaurentPolynomial<Fr>, scalar: Fr) -> LaurentPolynomial<Fr> {
    let mut out = LaurentPolynomial::<Fr>::zero();
    if scalar.is_zero() {
        return out;
    }
    for monomial in poly.monomials() {
        out.add_term(poly.coeff_of(monomial) * scalar, monomial.clone());
    }
    out
}

fn symbolic_gt_basis(setup: &SetupArtifacts) -> Vec<LaurentPolynomial<Fr>> {
    let num_pub = setup.lean_pk.vk.gamma_abc_g1.len();
    let domain_size = setup.oracle.a_mono[0].len();
    let z_poly = LaurentPolynomial::monomial(
        Fr::one(),
        LaurentMonomial::from_powers(&[("TAU", domain_size as i64)]),
    ) + LaurentPolynomial::monomial(-Fr::one(), LaurentMonomial::one());

    let mut omitted_forms_by_col = BTreeMap::<usize, Vec<Fr>>::new();
    for (i, j, form) in &setup.oracle.omitted_gap_mono {
        if *i == 0 {
            omitted_forms_by_col.insert(*j as usize, form.clone());
        }
    }

    let mut gt_sym = Vec::with_capacity(setup.pvugc_vk.t_const_points_gt.len());
    gt_sym.push(LaurentPolynomial::monomial(Fr::one(), LaurentMonomial::one()));
    for i in 0..setup.x_public.len() {
        let wit_col = num_pub + i;
        let form = omitted_forms_by_col
            .get(&wit_col)
            .cloned()
            .expect("missing omitted (0,j) symbolic form for T_i");
        gt_sym.push(to_lagrange_poly(&form) * z_poly.clone());
    }
    gt_sym
}

fn symbolic_t_component_target(setup: &SetupArtifacts) -> LaurentPolynomial<Fr> {
    let num_pub = setup.lean_pk.vk.gamma_abc_g1.len();
    let domain_size = setup.oracle.a_mono[0].len();
    let z_poly = LaurentPolynomial::monomial(
        Fr::one(),
        LaurentMonomial::from_powers(&[("TAU", domain_size as i64)]),
    ) + LaurentPolynomial::monomial(-Fr::one(), LaurentMonomial::one());

    let mut omitted_forms_by_col = BTreeMap::<usize, Vec<Fr>>::new();
    for (i, j, form) in &setup.oracle.omitted_gap_mono {
        if *i == 0 {
            omitted_forms_by_col.insert(*j as usize, form.clone());
        }
    }

    let mut target_poly = LaurentPolynomial::<Fr>::zero();
    for i in 0..setup.x_public.len() {
        let wit_col = num_pub + i;
        let target_form = omitted_forms_by_col
            .get(&wit_col)
            .cloned()
            .expect("missing omitted (0,j) symbolic form");
        target_poly = target_poly
            + LaurentPolynomial::monomial(setup.x_public[i], LaurentMonomial::one())
                * to_lagrange_poly(&target_form);
    }
    target_poly * z_poly * mono("RHO")
}

fn symbolic_full_decap_target(setup: &SetupArtifacts) -> LaurentPolynomial<Fr> {
    let num_pub = setup.lean_pk.vk.gamma_abc_g1.len();
    let mut ic_eval = LaurentPolynomial::zero();
    for i in 0..num_pub {
        let mut term = to_lagrange_poly(&setup.oracle.c_mono[i])
            + (mono("BETA") * to_lagrange_poly(&setup.oracle.a_mono[i]))
            + (mono("ALPHA") * to_lagrange_poly(&setup.oracle.b_mono[i]));
        if i > 0 {
            term = scale_poly(&term, setup.x_public[i - 1]);
        }
        ic_eval = ic_eval + term;
    }
    let r_raw_rho = ((mono("ALPHA") * mono("BETA")) + ic_eval) * mono("RHO");
    r_raw_rho + symbolic_t_component_target(setup)
}

fn serial_fft_g1(a: &mut [<E as Pairing>::G1], domain: &GeneralEvaluationDomain<Fr>) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let log_n = n.trailing_zeros();

    for k in 0..n {
        let rk = k.reverse_bits() >> (usize::BITS - log_n);
        if k < rk {
            a.swap(k, rk);
        }
    }

    let mut m = 1;
    while m < n {
        let omega_m = domain.element(domain.size() / (2 * m));
        for chunk in a.chunks_mut(2 * m) {
            let mut w = Fr::one();
            for j in 0..m {
                let t = chunk[j + m] * w;
                let u = chunk[j];
                chunk[j] = u + t;
                chunk[j + m] = u - t;
                w *= omega_m;
            }
        }
        m *= 2;
    }
}

fn serial_fft_scalar(a: &mut [Fr], domain: &GeneralEvaluationDomain<Fr>) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let log_n = n.trailing_zeros();
    for k in 0..n {
        let rk = k.reverse_bits() >> (usize::BITS - log_n);
        if k < rk {
            a.swap(k, rk);
        }
    }
    let mut m = 1;
    while m < n {
        let omega_m = domain.element(domain.size() / (2 * m));
        for chunk in a.chunks_mut(2 * m) {
            let mut w = Fr::one();
            for j in 0..m {
                let t = chunk[j + m] * w;
                let u = chunk[j];
                chunk[j] = u + t;
                chunk[j + m] = u - t;
                w *= omega_m;
            }
        }
        m *= 2;
    }
}

fn serial_ifft_g1(a: &mut [<E as Pairing>::G1], domain: &GeneralEvaluationDomain<Fr>) {
    serial_fft_g1(a, domain);
    if a.len() > 1 {
        a[1..].reverse();
    }
    let n_inv = domain
        .size_as_field_element()
        .inverse()
        .expect("domain size invertible");
    for x in a.iter_mut() {
        *x *= n_inv;
    }
}

fn precompute_form_bases_from_pk(
    pk: &ark_groth16::ProvingKey<E>,
    domain_size: usize,
) -> (Vec<<E as Pairing>::G1Affine>, Vec<<E as Pairing>::G1Affine>) {
    let domain = GeneralEvaluationDomain::<Fr>::new(domain_size)
        .or_else(|| GeneralEvaluationDomain::<Fr>::new(domain_size.next_power_of_two()))
        .expect("domain creation failed");

    let mut h_query_proj: Vec<_> = pk.h_query.iter().map(|p| p.into_group()).collect();
    if h_query_proj.len() < domain_size {
        h_query_proj.resize(domain_size, <E as Pairing>::G1::zero());
    } else {
        h_query_proj.truncate(domain_size);
    }
    serial_ifft_g1(&mut h_query_proj, &domain);
    let lagrange_srs: Vec<_> = h_query_proj.into_iter().map(|p| p.into_affine()).collect();

    let n_field = domain.size_as_field_element();
    let t0 = (n_field - Fr::one()) * (n_field + n_field).inverse().expect("2n invertible");
    let mut u = vec![Fr::zero(); domain_size];
    u[0] = t0;
    let mut denoms = Vec::with_capacity(domain_size.saturating_sub(1));
    let mut indices = Vec::with_capacity(domain_size.saturating_sub(1));
    for j in 1..domain_size {
        let omega_j = domain.element(j);
        denoms.push(n_field * (Fr::one() - omega_j));
        indices.push(j);
    }
    ark_ff::batch_inversion(&mut denoms);
    for (i, &j) in indices.iter().enumerate() {
        u[j] = denoms[i];
    }
    if domain_size > 1 {
        u[1..].reverse();
    }
    serial_fft_scalar(&mut u, &domain);

    let mut l_fft: Vec<_> = lagrange_srs.iter().map(|p| p.into_group()).collect();
    serial_fft_g1(&mut l_fft, &domain);
    for (l_val, &u_val) in l_fft.iter_mut().zip(u.iter()) {
        *l_val *= u_val;
    }
    serial_ifft_g1(&mut l_fft, &domain);
    let q_vector: Vec<_> = l_fft.into_iter().map(|p| p.into_affine()).collect();

    (lagrange_srs, q_vector)
}

fn form_to_g1_point(
    form: &[Fr],
    lagrange_srs: &[<E as Pairing>::G1Affine],
    q_vector: &[<E as Pairing>::G1Affine],
) -> Option<<E as Pairing>::G1Affine> {
    let domain_size = form.len() / 2;
    let mut bases = Vec::new();
    let mut scalars = Vec::new();

    for (k, coeff) in form.iter().take(domain_size).copied().enumerate() {
        if !coeff.is_zero() {
            bases.push(lagrange_srs[k]);
            scalars.push(coeff);
        }
    }
    for (k, coeff) in form.iter().skip(domain_size).copied().enumerate() {
        if !coeff.is_zero() {
            bases.push(q_vector[k]);
            scalars.push(coeff);
        }
    }

    if bases.is_empty() {
        return None;
    }
    let acc = <<E as Pairing>::G1 as VariableBaseMSM>::msm(&bases, &scalars).expect("msm");
    if acc.is_zero() {
        None
    } else {
        Some(acc.into_affine())
    }
}

fn compute_witness_bases_from_pk(
    pk: &ark_groth16::ProvingKey<E>,
    circuit: MockCircuit,
) -> (Vec<(u32, u32, <E as Pairing>::G1Affine)>, SymbolicOracleData) {
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
    let form_len = 2 * domain_size;

    let num_vars = cs.num_instance_variables() + cs.num_witness_variables();
    let mut col_a = vec![Vec::new(); num_vars];
    let mut col_b = vec![Vec::new(); num_vars];
    let mut col_c = vec![Vec::new(); num_vars];
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
    for (row, terms) in matrices.c.iter().enumerate() {
        if row < domain_size {
            for &(val, col) in terms {
                col_c[col].push((row, val));
            }
        }
    }

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

    let mut h_query_proj: Vec<_> = pk.h_query.iter().map(|p| p.into_group()).collect();
    if h_query_proj.len() < domain_size {
        h_query_proj.resize(domain_size, <E as Pairing>::G1::zero());
    } else {
        h_query_proj.truncate(domain_size);
    }
    serial_ifft_g1(&mut h_query_proj, &domain);
    let lagrange_srs: Vec<_> = h_query_proj.into_iter().map(|p| p.into_affine()).collect();

    let n_field = domain.size_as_field_element();
    let t0 = (n_field - Fr::one()) * (n_field + n_field).inverse().expect("2n invertible");
    let mut u = vec![Fr::zero(); domain_size];
    u[0] = t0;
    let mut denoms = Vec::with_capacity(domain_size.saturating_sub(1));
    let mut indices = Vec::with_capacity(domain_size.saturating_sub(1));
    for j in 1..domain_size {
        let omega_j = domain.element(j);
        denoms.push(n_field * (Fr::one() - omega_j));
        indices.push(j);
    }
    ark_ff::batch_inversion(&mut denoms);
    for (i, &j) in indices.iter().enumerate() {
        u[j] = denoms[i];
    }
    let inv_n_one_minus_omega = u.clone();
    let inv_domain_elements: Vec<_> = (0..domain_size)
        .map(|i| {
            let idx = if i == 0 { 0 } else { domain_size - i };
            domain.element(idx)
        })
        .collect();

    if domain_size > 1 {
        u[1..].reverse();
    }
    serial_fft_scalar(&mut u, &domain);
    let mut l_fft: Vec<_> = lagrange_srs.iter().map(|p| p.into_group()).collect();
    serial_fft_g1(&mut l_fft, &domain);
    for (l_val, &u_val) in l_fft.iter_mut().zip(u.iter()) {
        *l_val *= u_val;
    }
    serial_ifft_g1(&mut l_fft, &domain);
    let q_vector: Vec<_> = l_fft.into_iter().map(|p| p.into_affine()).collect();

    let domain_elements: Vec<_> = (0..domain_size).map(|i| domain.element(i)).collect();

    let compute_pair_form = |i_idx: usize, j_idx: usize| -> Option<Vec<Fr>> {
        let rows_u = &col_a[i_idx];
        let rows_v = &col_b[j_idx];
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
                    let wm = domain_elements[m];
                    let wk = domain_elements[k];
                    let d = if k >= m { k - m } else { k + domain_size - m };
                    let inv_denom = -(inv_domain_elements[m] * inv_n_one_minus_omega[d]);
                    let common = prod * inv_denom;
                    acc_u[idx_u] += common * wm;
                    acc_v[idx_v] -= common * wk;
                }
            }
        }

        let mut form = vec![Fr::zero(); form_len];
        for (idx_u, &(k, _)) in rows_u.iter().enumerate() {
            if !acc_u[idx_u].is_zero() {
                form[k] += acc_u[idx_u];
            }
        }
        for (idx_v, &(m, _)) in rows_v.iter().enumerate() {
            if !acc_v[idx_v].is_zero() {
                form[m] += acc_v[idx_v];
            }
        }
        if !diag_terms.is_empty() {
            diag_terms.sort_unstable_by_key(|(k, _)| *k);
            let mut cur_k = diag_terms[0].0;
            let mut cur_acc = Fr::zero();
            for (k, s) in diag_terms {
                if k != cur_k {
                    if !cur_acc.is_zero() {
                        form[domain_size + cur_k] += cur_acc;
                    }
                    cur_k = k;
                    cur_acc = s;
                } else {
                    cur_acc += s;
                }
            }
            if !cur_acc.is_zero() {
                form[domain_size + cur_k] += cur_acc;
            }
        }
        if form.iter().all(|c| c.is_zero()) {
            return None;
        }
        Some(form)
    };

    let compute_pair = |form: &[Fr]| -> Option<<E as Pairing>::G1Affine> {
        let mut pair_bases = Vec::new();
        let mut pair_scalars = Vec::new();
        for (k, coeff) in form.iter().take(domain_size).copied().enumerate() {
            if !coeff.is_zero() {
                pair_bases.push(lagrange_srs[k]);
                pair_scalars.push(coeff);
            }
        }
        for (k, coeff) in form.iter().skip(domain_size).copied().enumerate() {
            if !coeff.is_zero() {
                pair_bases.push(q_vector[k]);
                pair_scalars.push(coeff);
            }
        }
        if pair_bases.is_empty() {
            return None;
        }
        let h_acc = <<E as Pairing>::G1 as VariableBaseMSM>::msm(&pair_bases, &pair_scalars)
            .expect("msm");
        if h_acc.is_zero() {
            None
        } else {
            Some(h_acc.into_affine())
        }
    };

    let mut sorted_pairs: Vec<(usize, usize)> = active_pairs.into_iter().collect();
    sorted_pairs.sort();
    let mut h_wit = Vec::new();
    for (i, j) in sorted_pairs {
        if let Some(form) = compute_pair_form(i, j) {
            let p = compute_pair(&form).expect("non-zero form should map to non-zero point");
            h_wit.push((i as u32, j as u32, p));
        }
    }

    let mut omitted_gap_forms = Vec::new();
    for &j in &omit_const_wit_cols {
        if let Some(form) = compute_pair_form(0usize, j) {
            omitted_gap_forms.push((0u32, j as u32, form));
        }
    }

    let mut a_evals = vec![vec![Fr::zero(); domain_size]; num_vars];
    let mut b_evals = vec![vec![Fr::zero(); domain_size]; num_vars];
    let mut c_evals = vec![vec![Fr::zero(); domain_size]; num_vars];
    for col in 0..num_vars {
        for &(row, val) in &col_a[col] {
            if row < num_constraints {
                a_evals[col][row] += val;
            }
        }
        for &(row, val) in &col_b[col] {
            if row < num_constraints {
                b_evals[col][row] += val;
            }
        }
        for &(row, val) in &col_c[col] {
            if row < num_constraints {
                c_evals[col][row] += val;
            }
        }
    }

    let mut a_mono = a_evals;
    let mut b_mono = b_evals;
    let mut c_mono = c_evals;
    for col in 0..num_vars {
        domain.ifft_in_place(&mut a_mono[col]);
        domain.ifft_in_place(&mut b_mono[col]);
        domain.ifft_in_place(&mut c_mono[col]);
    }

    let poly_mul = |a: &[Fr], b: &[Fr]| -> Vec<Fr> {
        if a.is_empty() || b.is_empty() {
            return Vec::new();
        }
        let mut out = vec![Fr::zero(); a.len() + b.len() - 1];
        for (i, &ai) in a.iter().enumerate() {
            if ai.is_zero() {
                continue;
            }
            for (j, &bj) in b.iter().enumerate() {
                if bj.is_zero() {
                    continue;
                }
                out[i + j] += ai * bj;
            }
        }
        out
    };
    let div_by_xn_minus_1 = |mut p: Vec<Fr>, n: usize| -> Vec<Fr> {
        if n == 0 || p.len() <= n {
            return Vec::new();
        }
        let mut q = vec![Fr::zero(); p.len() - n];
        for k in (n..p.len()).rev() {
            let lead = p[k];
            if lead.is_zero() {
                continue;
            }
            q[k - n] += lead;
            p[k] = Fr::zero();
            p[k - n] += lead;
        }
        while matches!(q.last(), Some(c) if c.is_zero()) {
            q.pop();
        }
        q
    };

    let mut h_query_wit_mono = Vec::new();
    for (i, j, _) in &h_wit {
        let form = div_by_xn_minus_1(poly_mul(&a_mono[*i as usize], &b_mono[*j as usize]), domain_size);
        h_query_wit_mono.push((*i, *j, form));
    }
    let mut omitted_gap_mono = Vec::new();
    for (_, j, _) in &omitted_gap_forms {
        let form = div_by_xn_minus_1(poly_mul(&a_mono[0], &b_mono[*j as usize]), domain_size);
        omitted_gap_mono.push((0u32, *j, form));
    }

    (
        h_wit,
        SymbolicOracleData {
            h_query_wit_mono,
            omitted_gap_mono,
            omitted_gap_forms,
            a_mono,
            b_mono,
            c_mono,
        },
    )
}

fn build_setup(x_public: Vec<Fr>, rho: Fr) -> SetupArtifacts {
    let mut rng = StdRng::seed_from_u64(0xA11CE);
    let circuit = MockCircuit {
        x_public: x_public.clone(),
        y_private: vec![None; x_public.len()],
        z_private: None,
    };

    let (pk, vk) =
        Groth16::<E, PvugcReduction>::circuit_specific_setup(circuit.clone(), &mut rng).expect("setup");
    let (h_query_wit, oracle) = compute_witness_bases_from_pk(&pk, circuit);

    let num_pub = vk.gamma_abc_g1.len();
    let mut omitted_forms_by_col: BTreeMap<usize, Vec<Fr>> = BTreeMap::new();
    for (i, j, form) in &oracle.omitted_gap_forms {
        if *i == 0 {
            omitted_forms_by_col.insert(*j as usize, form.clone());
        }
    }
    let first_form = omitted_forms_by_col
        .values()
        .next()
        .expect("missing omitted (0,j) forms for mock public binding");
    let domain_size = first_form.len() / 2;
    let (lagrange_srs, q_vector) = precompute_form_bases_from_pk(&pk, domain_size);

    let mut t_const_points_gt = vec![PairingOutput::<E>(<<E as Pairing>::TargetField as One>::one())];
    for i in 0..x_public.len() {
        let wit_col = num_pub + i;
        let form = omitted_forms_by_col
            .get(&wit_col)
            .expect("missing omitted (0,j) form for mock public binding");
        let h_0j = form_to_g1_point(form, &lagrange_srs, &q_vector)
            .expect("non-zero omitted (0,j) form should map to non-zero point");
        t_const_points_gt.push(E::pairing(h_0j, vk.delta_g2));
    }

    let pvugc_vk = PvugcVk::new_with_all_witnesses_isolated(
        vk.beta_g2,
        vk.delta_g2,
        pk.b_g2_query.clone(),
        t_const_points_gt,
    );
    let lean_pk = LeanProvingKey {
        vk: vk.clone(),
        beta_g1: pk.beta_g1,
        delta_g1: pk.delta_g1,
        a_query_wit: pk.a_query.clone(),
        b_g1_query: pk.b_g1_query.clone(),
        h_query_wit,
        l_query: pk.l_query.clone(),
    };
    let bases = build_column_bases(&pvugc_vk, &vk, &x_public).unwrap();
    SetupArtifacts {
        lean_pk,
        vk,
        pvugc_vk,
        x_public,
        oracle,
        col_arms: arm_columns(&bases, &rho).unwrap()
    }
}

fn attack_from_ciphertext(setup: &SetupArtifacts) -> PairingOutput<E> {
    let vk = &setup.lean_pk.vk;
    let num_pub = vk.gamma_abc_g1.len();
    let domain_size = setup.oracle.a_mono[0].len();
    let z_poly = LaurentPolynomial::monomial(
        Fr::one(),
        LaurentMonomial::from_powers(&[("TAU", domain_size as i64)]),
    ) + LaurentPolynomial::monomial(-Fr::one(), LaurentMonomial::one());

    let mut g1_real = Vec::<<E as Pairing>::G1Affine>::new();
    let mut g1_sym = Vec::<LaurentPolynomial<Fr>>::new();
    for ((i, j, g1), (fi, fj, form)) in setup
        .lean_pk
        .h_query_wit
        .iter()
        .zip(setup.oracle.h_query_wit_mono.iter())
    {
        assert_eq!((*i, *j), (*fi, *fj));
        g1_real.push(*g1);
        g1_sym.push(to_lagrange_poly(form) * z_poly.clone() * mono("DELTA_INV"));
    }
    for (col, g1) in setup.lean_pk.a_query_wit.iter().copied().enumerate() {
        g1_real.push(g1);
        g1_sym.push(to_lagrange_poly(&setup.oracle.a_mono[col]));
    }
    for (col, g1) in setup.lean_pk.b_g1_query.iter().copied().enumerate() {
        g1_real.push(g1);
        g1_sym.push(to_lagrange_poly(&setup.oracle.b_mono[col]));
    }
    for (idx, g1) in setup.lean_pk.l_query.iter().copied().enumerate() {
        let col = num_pub + idx;
        let expr = to_lagrange_poly(&setup.oracle.c_mono[col])
            + (mono("BETA") * to_lagrange_poly(&setup.oracle.a_mono[col]))
            + (mono("ALPHA") * to_lagrange_poly(&setup.oracle.b_mono[col]));
        g1_real.push(g1);
        g1_sym.push(expr * mono("DELTA_INV"));
    }
    g1_real.push(vk.alpha_g1);
    g1_sym.push(mono("ALPHA"));
    g1_real.push(setup.lean_pk.beta_g1);
    g1_sym.push(mono("BETA"));
    g1_real.push(setup.lean_pk.delta_g1);
    g1_sym.push(mono("DELTA"));
    for (i, g) in vk.gamma_abc_g1.iter().copied().enumerate() {
        let expr = to_lagrange_poly(&setup.oracle.c_mono[i])
            + (mono("BETA") * to_lagrange_poly(&setup.oracle.a_mono[i]))
            + (mono("ALPHA") * to_lagrange_poly(&setup.oracle.b_mono[i]));
        g1_real.push(g);
        g1_sym.push(expr * mono("GAMMA_INV"));
    }

    let mut g2_real = Vec::<<E as Pairing>::G2Affine>::new();
    let mut g2_sym = Vec::<LaurentPolynomial<Fr>>::new();
    for (i, y) in setup.col_arms.y_cols_rho.iter().copied().enumerate() {
        g2_real.push(y);
        if i == 0 {
            let mut y_public_leg = mono("BETA") + to_lagrange_poly(&setup.oracle.b_mono[0]);
            for j in 0..setup.x_public.len() {
                y_public_leg = y_public_leg
                    + LaurentPolynomial::monomial(setup.x_public[j], LaurentMonomial::one())
                        * to_lagrange_poly(&setup.oracle.b_mono[1 + j]);
            }
            g2_sym.push(y_public_leg * mono("RHO"));
        } else {
            let b_col = num_pub + (i - 1);
            g2_sym.push(to_lagrange_poly(&setup.oracle.b_mono[b_col]) * mono("RHO"));
        }
    }
    g2_real.push(setup.col_arms.delta_rho);
    g2_sym.push(mono("DELTA") * mono("RHO"));

    let gt_real = setup.pvugc_vk.t_const_points_gt.as_ref().to_vec();
    let gt_sym = symbolic_gt_basis(setup);

    let constructible = build_constructible_elements(&g1_sym, &g2_sym, &gt_sym);
    let target_poly = symbolic_full_decap_target(setup);
    let solution = solve_target_from_constructible(&constructible, &target_poly)
        .expect("symbolic solve for full decapsulation target");

    let pairings_real: Vec<Vec<PairingOutput<E>>> = g1_real
        .iter()
        .map(|g1| g2_real.iter().map(|g2| E::pairing(*g1, *g2)).collect())
        .collect();

    let mut recovered = PairingOutput::<E>(<<E as Pairing>::TargetField as One>::one());
    for term in &solution.terms {
        match term.kind {
            ConstructibleKind::Pairing { g1_index, g2_index } => {
                let gt = pairings_real[g1_index][g2_index];
                recovered += PairingOutput::<E>(gt.0.pow(&term.coeff.into_bigint()));
            }
            ConstructibleKind::GtElement { gt_index } => {
                let gt = gt_real[gt_index];
                recovered += PairingOutput::<E>(gt.0.pow(&term.coeff.into_bigint()));
            }
        }
    }

    recovered
}

#[test]
fn attack() {
    pvugc_setup_check::pvugc_setup_checks();

    let seed = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock")
        .as_nanos() as u64;
    let mut rng = StdRng::seed_from_u64(seed);
    let rho = Fr::rand(&mut rng);
    assert!(
        Fr::from(5u64).sqrt().is_none(),
        "attack statement must be unsatisfiable"
    );

    let setup = build_setup(vec![Fr::from(5u64), Fr::from(11u64), Fr::from(13u64)], rho);
    let recovered_k = attack_from_ciphertext(&setup);

    let r_baked = compute_baked_target(&setup.vk, &setup.pvugc_vk, &setup.x_public)
        .expect("compute_baked_target");
    let k_target_backdoor = compute_r_to_rho(&r_baked, &rho);
    assert_eq!(recovered_k, k_target_backdoor);
}
