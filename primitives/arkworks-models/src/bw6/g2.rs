use ark_serialize::*;
use ark_std::vec::Vec;
use derivative::Derivative;

use crate::{
	bw6::BW6Config,
	short_weierstrass::{Affine, Projective},
	AffineRepr, CurveGroup,
};

pub type G2Affine<P> = Affine<<P as BW6Config>::G2Config>;
pub type G2Projective<P> = Projective<<P as BW6Config>::G2Config>;

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
	Copy(bound = "P: BW6Config"),
	Clone(bound = "P: BW6Config"),
	Debug(bound = "P: BW6Config"),
	PartialEq(bound = "P: BW6Config"),
	Eq(bound = "P: BW6Config")
)]
pub struct G2Prepared<P: BW6Config>(pub G2Affine<P>);

impl<P: BW6Config> From<G2Affine<P>> for G2Prepared<P> {
	fn from(other: G2Affine<P>) -> Self {
		G2Prepared(other)
	}
}

impl<P: BW6Config> From<G2Projective<P>> for G2Prepared<P> {
	fn from(q: G2Projective<P>) -> Self {
		q.into_affine().into()
	}
}

impl<'a, P: BW6Config> From<&'a G2Affine<P>> for G2Prepared<P> {
	fn from(other: &'a G2Affine<P>) -> Self {
		G2Prepared(*other)
	}
}

impl<'a, P: BW6Config> From<&'a G2Projective<P>> for G2Prepared<P> {
	fn from(q: &'a G2Projective<P>) -> Self {
		q.into_affine().into()
	}
}

impl<P: BW6Config> G2Prepared<P> {
	pub fn is_zero(&self) -> bool {
		self.0.infinity
	}
}

impl<P: BW6Config> Default for G2Prepared<P> {
	fn default() -> Self {
		G2Prepared(G2Affine::<P>::generator())
	}
}
