use crate::error::Error;
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

#[derive(Clone, Debug)]
pub struct ColumnBases<E: Pairing> {
    pub y_cols: Vec<E::G2Affine>,
    pub delta: E::G2Affine,
}

impl<E: Pairing> ColumnBases<E> {
    pub fn validate_subgroups(&self) -> crate::error::Result<()> {
        use ark_ff::PrimeField;
        let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
        let in_prime_subgroup_g2 = |g: &E::G2Affine| {
            if g.is_zero() {
                return true;
            }
            g.mul_bigint(order).is_zero()
        };

        for y in &self.y_cols {
            if !in_prime_subgroup_g2(y) {
                return Err(Error::InvalidSubgroup);
            }
        }
        if self.delta.is_zero() {
            return Err(Error::ZeroDelta);
        }
        if !in_prime_subgroup_g2(&self.delta) {
            return Err(Error::InvalidSubgroup);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ColumnArms<E: Pairing> {
    pub y_cols_rho: Vec<E::G2Affine>,
    pub delta_rho: E::G2Affine,
}

pub fn arm_columns<E: Pairing>(
    bases: &ColumnBases<E>,
    rho: &E::ScalarField,
) -> crate::error::Result<ColumnArms<E>> {
    if rho.is_zero() {
        return Err(Error::ZeroRho);
    }
    if bases.delta.is_zero() {
        return Err(Error::ZeroDelta);
    }
    let y_cols_rho: Vec<_> = bases
        .y_cols
        .iter()
        .map(|y| (y.into_group() * rho).into_affine())
        .collect();
    let delta_rho = (bases.delta.into_group() * rho).into_affine();
    Ok(ColumnArms {
        y_cols_rho,
        delta_rho,
    })
}
