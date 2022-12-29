use crate::{
	models::{short_weierstrass::SWCurveConfig, CurveConfig},
	pairing::{MillerLoopOutput, Pairing, PairingOutput},
};
use ark_ff::fields::{
	fp3::Fp3Config,
	fp6_2over3::{Fp6, Fp6Config},
	PrimeField,
};
use derivative::Derivative;

use ark_std::marker::PhantomData;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub enum TwistType {
	M,
	D,
}

pub trait BW6Config: 'static + Eq + Sized {
	const X: <Self::Fp as PrimeField>::BigInt;
	const X_IS_NEGATIVE: bool;
	const ATE_LOOP_COUNT_1: &'static [u64];
	const ATE_LOOP_COUNT_1_IS_NEGATIVE: bool;
	const ATE_LOOP_COUNT_2: &'static [i8];
	const ATE_LOOP_COUNT_2_IS_NEGATIVE: bool;
	const TWIST_TYPE: TwistType;
	type Fp: PrimeField + Into<<Self::Fp as PrimeField>::BigInt>;
	type Fp3Config: Fp3Config<Fp = Self::Fp>;
	type Fp6Config: Fp6Config<Fp3Config = Self::Fp3Config>;
	type G1Config: SWCurveConfig<BaseField = Self::Fp>;
	type G2Config: SWCurveConfig<
		BaseField = Self::Fp,
		ScalarField = <Self::G1Config as CurveConfig>::ScalarField,
	>;

	fn final_exponentiation(f: MillerLoopOutput<BW6<Self>>) -> Option<PairingOutput<BW6<Self>>>;

	fn multi_miller_loop(
		a: impl IntoIterator<Item = impl Into<G1Prepared<Self>>>,
		b: impl IntoIterator<Item = impl Into<G2Prepared<Self>>>,
	) -> MillerLoopOutput<BW6<Self>>;
}

pub mod g1;
pub mod g2;

pub use self::{
	g1::{G1Affine, G1Prepared, G1Projective},
	g2::{G2Affine, G2Prepared, G2Projective},
};

#[derive(Derivative)]
#[derivative(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct BW6<P: BW6Config>(PhantomData<fn() -> P>);

impl<P: BW6Config> Pairing for BW6<P> {
	type BaseField = <P::G1Config as CurveConfig>::BaseField;
	type ScalarField = <P::G1Config as CurveConfig>::ScalarField;
	type G1 = G1Projective<P>;
	type G1Affine = G1Affine<P>;
	type G1Prepared = G1Prepared<P>;
	type G2 = G2Projective<P>;
	type G2Affine = G2Affine<P>;
	type G2Prepared = G2Prepared<P>;
	type TargetField = Fp6<P::Fp6Config>;

	fn final_exponentiation(f: MillerLoopOutput<Self>) -> Option<PairingOutput<Self>> {
		P::final_exponentiation(f)
	}

	fn multi_miller_loop(
		a: impl IntoIterator<Item = impl Into<Self::G1Prepared>>,
		b: impl IntoIterator<Item = impl Into<Self::G2Prepared>>,
	) -> MillerLoopOutput<Self> {
		P::multi_miller_loop(a, b)
	}
}
