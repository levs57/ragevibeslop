pub mod arming;
pub mod audit_circuit;
pub mod decap;
pub mod error;
pub mod ppe;
pub mod symbolic_attack;

use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, One, PrimeField};
use ark_groth16::VerifyingKey as Groth16VK;
use std::ops::Neg;

pub use arming::{arm_columns, ColumnArms, ColumnBases};
pub use decap::{decap as decapsulate, prove_and_build_commitments, OneSidedCommitments};
pub use error::{Error, Result};
pub use ppe::{compute_baked_target, compute_groth16_target, PvugcVk};

fn split_statement_only_bases<E: Pairing>(
    pvugc_vk: &PvugcVk<E>,
    vk: &Groth16VK<E>,
    public_inputs: &[E::ScalarField],
) -> Result<(E::G2Affine, Vec<E::G2Affine>)> {
    let total_instance = vk.gamma_abc_g1.len();
    if total_instance == 0 {
        return Err(Error::MismatchedSizes);
    }
    let expected_inputs = total_instance.saturating_sub(1);
    if public_inputs.len() != expected_inputs {
        return Err(Error::PublicInputLength {
            expected: expected_inputs,
            actual: public_inputs.len(),
        });
    }
    let required_bases = 1 + total_instance;
    if pvugc_vk.b_g2_query.len() < required_bases {
        return Err(Error::MismatchedSizes);
    }

    let mut aggregate = pvugc_vk.beta_g2.into_group();
    aggregate += pvugc_vk.b_g2_query[0].into_group();
    for (idx, public_val) in public_inputs.iter().enumerate() {
        let base = pvugc_vk
            .b_g2_query
            .get(1 + idx)
            .ok_or(Error::MismatchedSizes)?;
        aggregate += base.into_group() * public_val;
    }

    let witness_bases: Vec<E::G2Affine> = pvugc_vk
        .b_g2_query
        .iter()
        .skip(total_instance)
        .cloned()
        .collect();

    Ok((aggregate.into_affine(), witness_bases))
}

pub fn build_column_bases<E: Pairing>(
    pvugc_vk: &PvugcVk<E>,
    vk: &Groth16VK<E>,
    public_inputs: &[E::ScalarField],
) -> Result<ColumnBases<E>> {
    let (public_leg, witness_cols) = split_statement_only_bases(pvugc_vk, vk, public_inputs)?;
    let mut y_cols = Vec::with_capacity(1 + witness_cols.len());
    y_cols.push(public_leg);
    y_cols.extend(witness_cols);

    let gamma = vk.gamma_g2;
    let gamma_neg = gamma.into_group().neg().into_affine();
    for (idx, y) in y_cols.iter().enumerate() {
        if *y == gamma || *y == gamma_neg {
            return Err(Error::DegenerateTarget);
        }
        if idx == 0 && y.is_zero() {
            return Err(Error::DegenerateTarget);
        }
    }

    let bases = ColumnBases {
        y_cols,
        delta: pvugc_vk.delta_g2,
    };
    bases.validate_subgroups()?;
    Ok(bases)
}

pub fn compute_r_to_rho<E: Pairing>(
    r: &PairingOutput<E>,
    rho: &E::ScalarField,
) -> PairingOutput<E> {
    PairingOutput(r.0.pow(&rho.into_bigint()))
}

pub fn setup_and_arm<E: Pairing>(
    pvugc_vk: &PvugcVk<E>,
    vk: &Groth16VK<E>,
    public_inputs: &[E::ScalarField],
    rho: &E::ScalarField,
) -> Result<(
    ColumnBases<E>,
    ColumnArms<E>,
    PairingOutput<E>,
    PairingOutput<E>,
)> {
    if !ppe::validate_pvugc_vk_subgroups(pvugc_vk) {
        return Err(Error::InvalidSubgroup);
    }
    if !ppe::validate_groth16_vk_subgroups(vk) {
        return Err(Error::InvalidSubgroup);
    }
    let r_baked = compute_baked_target(vk, pvugc_vk, public_inputs)?;
    if r_baked.0.is_one() {
        return Err(Error::DegenerateTarget);
    }
    let bases = build_column_bases(pvugc_vk, vk, public_inputs)?;
    let col_arms = arm_columns(&bases, rho)?;
    let k = compute_r_to_rho(&r_baked, rho);
    Ok((bases, col_arms, r_baked, k))
}
