use crate::bls12::Bls12Config;
use ark_ec::{
	short_weierstrass::{Affine, Projective},
	AffineRepr, CurveGroup,
};
use ark_serialize::*;
use ark_std::vec::Vec;
use derivative::Derivative;

pub type G2Affine<P> = Affine<<P as Bls12Config>::G2Config>;
pub type G2Projective<P> = Projective<<P as Bls12Config>::G2Config>;

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
	Clone(bound = "P: Bls12Config"),
	Debug(bound = "P: Bls12Config"),
	PartialEq(bound = "P: Bls12Config"),
	Eq(bound = "P: Bls12Config")
)]
pub struct G2Prepared<P: Bls12Config>(pub G2Affine<P>);

impl<P: Bls12Config> From<G2Affine<P>> for G2Prepared<P> {
	fn from(other: G2Affine<P>) -> Self {
		G2Prepared(other)
	}
}

impl<P: Bls12Config> From<G2Projective<P>> for G2Prepared<P> {
	fn from(q: G2Projective<P>) -> Self {
		q.into_affine().into()
	}
}

impl<'a, P: Bls12Config> From<&'a G2Affine<P>> for G2Prepared<P> {
	fn from(other: &'a G2Affine<P>) -> Self {
		G2Prepared(*other)
	}
}

impl<'a, P: Bls12Config> From<&'a G2Projective<P>> for G2Prepared<P> {
	fn from(q: &'a G2Projective<P>) -> Self {
		q.into_affine().into()
	}
}

impl<P: Bls12Config> G2Prepared<P> {
	pub fn is_zero(&self) -> bool {
		self.0.is_zero()
	}
}

impl<P: Bls12Config> Default for G2Prepared<P> {
	fn default() -> Self {
		G2Prepared(G2Affine::<P>::generator())
	}
}
