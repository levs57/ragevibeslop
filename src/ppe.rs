use crate::error::{Error, Result};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::AffineRepr;
use ark_ff::{Field, One, PrimeField};
use ark_groth16::VerifyingKey as Groth16VK;
use ark_std::Zero;

#[derive(Clone, Debug)]
pub struct PvugcVk<E: Pairing> {
    pub beta_g2: E::G2Affine,
    pub delta_g2: E::G2Affine,
    pub b_g2_query: std::sync::Arc<Vec<E::G2Affine>>,
    pub t_const_points_gt: std::sync::Arc<Vec<PairingOutput<E>>>,
}

impl<E: Pairing> PvugcVk<E> {
    pub fn new_with_all_witnesses_isolated(
        beta_g2: E::G2Affine,
        delta_g2: E::G2Affine,
        b_g2_query: Vec<E::G2Affine>,
        t_const_points_gt: Vec<PairingOutput<E>>,
    ) -> Self {
        Self {
            beta_g2,
            delta_g2,
            b_g2_query: std::sync::Arc::new(b_g2_query),
            t_const_points_gt: std::sync::Arc::new(t_const_points_gt),
        }
    }
}

pub fn validate_pvugc_vk_subgroups<E: Pairing>(pvugc_vk: &PvugcVk<E>) -> bool {
    let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
    let is_good = |g: &E::G2Affine| {
        if g.is_zero() {
            return true;
        }
        g.mul_bigint(order).is_zero()
    };

    if pvugc_vk.b_g2_query.is_empty() {
        return false;
    }
    if pvugc_vk.beta_g2.is_zero() || !is_good(&pvugc_vk.beta_g2) {
        return false;
    }
    if pvugc_vk.delta_g2.is_zero() || !is_good(&pvugc_vk.delta_g2) {
        return false;
    }
    if pvugc_vk.b_g2_query.iter().any(|g| !is_good(g)) {
        return false;
    }

    let is_good_gt = |g: &PairingOutput<E>| {
        if g.0.is_zero() {
            return false;
        }
        let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
        g.0.pow(order).is_one()
    };
    if pvugc_vk.t_const_points_gt.iter().any(|g| !is_good_gt(g)) {
        return false;
    }
    true
}

pub fn validate_groth16_vk_subgroups<E: Pairing>(vk: &Groth16VK<E>) -> bool {
    let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
    let is_good_g1 = |g: &E::G1Affine| {
        if g.is_zero() {
            return true;
        }
        g.mul_bigint(order).is_zero()
    };
    let is_good_g2 = |g: &E::G2Affine| {
        if g.is_zero() {
            return true;
        }
        g.mul_bigint(order).is_zero()
    };
    if vk.alpha_g1.is_zero() || !is_good_g1(&vk.alpha_g1) {
        return false;
    }
    if vk.beta_g2.is_zero() || !is_good_g2(&vk.beta_g2) {
        return false;
    }
    if vk.gamma_g2.is_zero() || !is_good_g2(&vk.gamma_g2) {
        return false;
    }
    if vk.delta_g2.is_zero() || !is_good_g2(&vk.delta_g2) {
        return false;
    }
    if vk.gamma_abc_g1.iter().any(|g| !is_good_g1(g)) {
        return false;
    }
    true
}

pub fn compute_groth16_target<E: Pairing>(
    vk: &Groth16VK<E>,
    public_inputs: &[E::ScalarField],
) -> Result<PairingOutput<E>> {
    let ic_bases = &vk.gamma_abc_g1;
    let expected_inputs = ic_bases.len().saturating_sub(1);
    if public_inputs.len() != expected_inputs {
        return Err(Error::PublicInputLength {
            expected: expected_inputs,
            actual: public_inputs.len(),
        });
    }

    let mut l = ic_bases[0].into_group();
    for (gamma, x_i) in ic_bases.iter().skip(1).zip(public_inputs.iter()) {
        l += gamma.into_group() * x_i;
    }
    if l.is_zero() {
        return Err(Error::ZeroInstanceCommitment);
    }

    let r = E::pairing(vk.alpha_g1, vk.beta_g2) + E::pairing(l, vk.gamma_g2);
    if r.0.is_one() || r.0.is_zero() {
        return Err(Error::DegenerateTarget);
    }
    Ok(r)
}

pub fn compute_baked_target<E: Pairing>(
    vk: &Groth16VK<E>,
    pvugc_vk: &PvugcVk<E>,
    public_inputs: &[E::ScalarField],
) -> Result<PairingOutput<E>> {
    let r_raw = compute_groth16_target(vk, public_inputs)?;
    if pvugc_vk.t_const_points_gt.len() != public_inputs.len() + 1 {
        return Err(Error::MismatchedSizes);
    }

    let mut t_acc = pvugc_vk.t_const_points_gt[0];
    for (i, x_i) in public_inputs.iter().enumerate() {
        let term = pvugc_vk.t_const_points_gt[i + 1].0.pow(&x_i.into_bigint());
        t_acc = PairingOutput(t_acc.0 * term);
    }
    Ok(r_raw + t_acc)
}

