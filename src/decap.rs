use crate::arming::ColumnArms;
use crate::error::{Error, Result};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalSerialize;
use sha2::{Digest, Sha256};
use std::ops::Neg;

#[derive(Clone, Debug)]
pub struct OneSidedCommitments<E: Pairing> {
    pub x_b_cols: Vec<(E::G1Affine, E::G1Affine)>,
    pub theta: Vec<(E::G1Affine, E::G1Affine)>,
    pub theta_delta_cancel: (E::G1Affine, E::G1Affine),
}

pub fn build_commitments<E: Pairing>(
    a: &E::G1Affine,
    c: &E::G1Affine,
    s: &E::ScalarField,
    full_assignment: &[E::ScalarField],
    num_instance: usize,
) -> OneSidedCommitments<E> {
    let a_g = a.into_group();
    let public_count = num_instance;
    assert!(public_count <= full_assignment.len());
    let witness_count = full_assignment.len().saturating_sub(public_count);
    let mut x_b_cols: Vec<(E::G1Affine, E::G1Affine)> = Vec::with_capacity(1 + witness_count);
    x_b_cols.push((*a, E::G1Affine::zero()));

    for b in full_assignment.iter().skip(public_count) {
        x_b_cols.push(((a_g * b).into_affine(), E::G1Affine::zero()));
    }

    let theta0 = ((a_g * s) - c.into_group()).into_affine();

    let mut h = Sha256::new();
    let mut buf = Vec::new();
    a.serialize_compressed(&mut buf).unwrap();
    h.update(&buf);
    buf.clear();
    c.serialize_compressed(&mut buf).unwrap();
    h.update(&buf);
    buf.clear();
    h.update(&s.into_bigint().to_bytes_be());
    let bytes = h.finalize();
    let r_theta = E::ScalarField::from_le_bytes_mod_order(&bytes);
    let rand_limb = (a_g * r_theta).into_affine();

    let theta = vec![(theta0, rand_limb)];
    let theta_delta_cancel = (rand_limb.into_group().neg().into_affine(), E::G1Affine::zero());
    OneSidedCommitments {
        x_b_cols,
        theta,
        theta_delta_cancel,
    }
}

pub fn decap<E: Pairing>(
    commitments: &OneSidedCommitments<E>,
    col_arms: &ColumnArms<E>,
) -> Result<PairingOutput<E>> {
    if commitments.x_b_cols.len() != col_arms.y_cols_rho.len() {
        return Err(Error::MismatchedSizes);
    }

    use ark_std::One;
    let mut k = PairingOutput::<E>(One::one());
    let safe_pairing = |g1: E::G1Affine, g2: E::G2Affine| -> PairingOutput<E> {
        if g1.is_zero() || g2.is_zero() {
            PairingOutput::<E>(One::one())
        } else {
            E::pairing(g1, g2)
        }
    };

    let num_cols = commitments.x_b_cols.len();
    for i in 0..num_cols {
        let (x0, x1) = commitments.x_b_cols[i];
        let y_rho = col_arms.y_cols_rho[i];
        k += safe_pairing(x0, y_rho);
        k += safe_pairing(x1, y_rho);
    }
    let num_theta = commitments.theta.len();
    for i in 0..num_theta {
        let (t0, t1) = commitments.theta[i];
        k += safe_pairing(t0, col_arms.delta_rho);
        k += safe_pairing(t1, col_arms.delta_rho);
    }
    let (c0, c1) = commitments.theta_delta_cancel;
    k += safe_pairing(c0, col_arms.delta_rho);
    k += safe_pairing(c1, col_arms.delta_rho);
    Ok(k)
}

pub fn prove_and_build_commitments<E, C, R>(
    pk: &ark_groth16::ProvingKey<E>,
    circuit: C,
    rng: &mut R,
) -> core::result::Result<
    (
        ark_groth16::Proof<E>,
        OneSidedCommitments<E>,
        Vec<E::ScalarField>,
        E::ScalarField,
    ),
    ark_relations::r1cs::SynthesisError,
>
where
    E: Pairing,
    C: ark_relations::r1cs::ConstraintSynthesizer<E::ScalarField>,
    R: ark_std::rand::Rng,
{
    use ark_ff::UniformRand;
    use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal};

    let r = E::ScalarField::rand(rng);
    let s = E::ScalarField::rand(rng);

    let cs = ConstraintSystem::<E::ScalarField>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    circuit.generate_constraints(cs.clone())?;
    cs.finalize();

    let matrices = cs.to_matrices().expect("matrix extraction");
    let prover = cs.borrow().unwrap();
    let full_assignment: Vec<E::ScalarField> = [
        prover.instance_assignment.as_slice(),
        prover.witness_assignment.as_slice(),
    ]
    .concat();
    let num_inputs = prover.instance_assignment.len();

    use ark_groth16::r1cs_to_qap::PvugcReduction;
    let proof = ark_groth16::Groth16::<E, PvugcReduction>::create_proof_with_reduction_and_matrices(
        pk,
        r,
        s,
        &matrices,
        num_inputs,
        cs.num_constraints(),
        &full_assignment,
    )?;

    let commitments = build_commitments(&proof.a, &proof.c, &s, &full_assignment, num_inputs);
    Ok((proof, commitments, full_assignment, s))
}
