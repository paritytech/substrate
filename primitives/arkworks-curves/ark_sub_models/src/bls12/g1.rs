use crate::bls12::Bls12Config;
use ark_ec::{
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};
use ark_serialize::*;
use ark_std::vec::Vec;

use derivative::Derivative;

pub type G1Affine<P> = Affine<<P as Bls12Config>::G1Config>;
pub type G1Projective<P> = Projective<<P as Bls12Config>::G1Config>;

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Clone(bound = "P: Bls12Config"),
    Debug(bound = "P: Bls12Config"),
    PartialEq(bound = "P: Bls12Config"),
    Eq(bound = "P: Bls12Config")
)]
pub struct G1Prepared<P: Bls12Config>(pub G1Affine<P>);

impl<P: Bls12Config> From<G1Affine<P>> for G1Prepared<P> {
    fn from(other: G1Affine<P>) -> Self {
        G1Prepared(other)
    }
}

impl<P: Bls12Config> From<G1Projective<P>> for G1Prepared<P> {
    fn from(q: G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<'a, P: Bls12Config> From<&'a G1Affine<P>> for G1Prepared<P> {
    fn from(other: &'a G1Affine<P>) -> Self {
        G1Prepared(*other)
    }
}

impl<'a, P: Bls12Config> From<&'a G1Projective<P>> for G1Prepared<P> {
    fn from(q: &'a G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: Bls12Config> G1Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<P: Bls12Config> Default for G1Prepared<P> {
    fn default() -> Self {
        G1Prepared(G1Affine::<P>::generator())
    }
}
