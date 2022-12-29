use crate::{
    bw6::BW6Config,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};
use ark_serialize::*;
use ark_std::vec::Vec;

pub type G1Affine<P> = Affine<<P as BW6Config>::G1Config>;
pub type G1Projective<P> = Projective<<P as BW6Config>::G1Config>;

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Copy(bound = "P: BW6Config"),
    Clone(bound = "P: BW6Config"),
    Debug(bound = "P: BW6Config"),
    PartialEq(bound = "P: BW6Config"),
    Eq(bound = "P: BW6Config")
)]
pub struct G1Prepared<P: BW6Config>(pub G1Affine<P>);

impl<P: BW6Config> From<G1Affine<P>> for G1Prepared<P> {
    fn from(other: G1Affine<P>) -> Self {
        G1Prepared(other)
    }
}

impl<P: BW6Config> From<G1Projective<P>> for G1Prepared<P> {
    fn from(q: G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<'a, P: BW6Config> From<&'a G1Affine<P>> for G1Prepared<P> {
    fn from(other: &'a G1Affine<P>) -> Self {
        G1Prepared(*other)
    }
}

impl<'a, P: BW6Config> From<&'a G1Projective<P>> for G1Prepared<P> {
    fn from(q: &'a G1Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: BW6Config> G1Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.0.infinity
    }
}

impl<P: BW6Config> Default for G1Prepared<P> {
    fn default() -> Self {
        G1Prepared(G1Affine::<P>::generator())
    }
}
