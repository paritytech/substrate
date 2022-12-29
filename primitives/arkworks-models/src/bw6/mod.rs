use crate::{
	models::{short_weierstrass::SWCurveConfig, CurveConfig},
	pairing::{MillerLoopOutput, Pairing, PairingOutput},
};
use ark_ff::{
	fields::{
		fp3::Fp3Config,
		fp6_2over3::{Fp6, Fp6Config},
		Field, PrimeField,
	},
	BitIteratorBE, CyclotomicMultSubgroup,
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

impl<P: BW6Config> BW6<P> {
	// Evaluate the line function at point p.
	fn ell(f: &mut Fp6<P::Fp6Config>, coeffs: &(P::Fp, P::Fp, P::Fp), p: &G1Affine<P>) {
		let mut c0 = coeffs.0;
		let mut c1 = coeffs.1;
		let mut c2 = coeffs.2;

		match P::TWIST_TYPE {
			TwistType::M => {
				c2 *= &p.y;
				c1 *= &p.x;
				f.mul_by_014(&c0, &c1, &c2);
			},
			TwistType::D => {
				c0 *= &p.y;
				c1 *= &p.x;
				f.mul_by_034(&c0, &c1, &c2);
			},
		}
	}

	fn exp_by_x(mut f: Fp6<P::Fp6Config>) -> Fp6<P::Fp6Config> {
		f = f.cyclotomic_exp(&P::X);
		if P::X_IS_NEGATIVE {
			f.cyclotomic_inverse_in_place();
		}
		f
	}

	fn final_exponentiation_first_chunk(
		elt: &Fp6<P::Fp6Config>,
		elt_inv: &Fp6<P::Fp6Config>,
	) -> Fp6<P::Fp6Config> {
		// (q^3-1)*(q+1)

		// elt_q3 = elt^(q^3)
		let mut elt_q3 = *elt;
		elt_q3.cyclotomic_inverse_in_place();
		// elt_q3_over_elt = elt^(q^3-1)
		let elt_q3_over_elt = elt_q3 * elt_inv;
		// alpha = elt^((q^3-1) * q)
		let mut alpha = elt_q3_over_elt;
		alpha.frobenius_map_in_place(1);
		// beta = elt^((q^3-1)*(q+1)
		alpha * &elt_q3_over_elt
	}

	#[allow(clippy::let_and_return)]
	fn final_exponentiation_last_chunk(f: &Fp6<P::Fp6Config>) -> Fp6<P::Fp6Config> {
		// hard_part
		// From https://eprint.iacr.org/2020/351.pdf, Alg.6

		#[rustfmt::skip]
        // R0(x) := (-103*x^7 + 70*x^6 + 269*x^5 - 197*x^4 - 314*x^3 - 73*x^2 - 263*x - 220)
        // R1(x) := (103*x^9 - 276*x^8 + 77*x^7 + 492*x^6 - 445*x^5 - 65*x^4 + 452*x^3 - 181*x^2 + 34*x + 229)
        // f ^ R0(u) * (f ^ q) ^ R1(u) in a 2-NAF multi-exp fashion.

        // steps 1,2,3
        let f0 = *f;
		let mut f0p = f0;
		f0p.frobenius_map_in_place(1);
		let f1 = Self::exp_by_x(f0);
		let mut f1p = f1;
		f1p.frobenius_map_in_place(1);
		let f2 = Self::exp_by_x(f1);
		let mut f2p = f2;
		f2p.frobenius_map_in_place(1);
		let f3 = Self::exp_by_x(f2);
		let mut f3p = f3;
		f3p.frobenius_map_in_place(1);
		let f4 = Self::exp_by_x(f3);
		let mut f4p = f4;
		f4p.frobenius_map_in_place(1);
		let f5 = Self::exp_by_x(f4);
		let mut f5p = f5;
		f5p.frobenius_map_in_place(1);
		let f6 = Self::exp_by_x(f5);
		let mut f6p = f6;
		f6p.frobenius_map_in_place(1);
		let f7 = Self::exp_by_x(f6);
		let mut f7p = f7;
		f7p.frobenius_map_in_place(1);

		// step 4
		let f8p = Self::exp_by_x(f7p);
		let f9p = Self::exp_by_x(f8p);

		// step 5
		let mut f5p_p3 = f5p;
		f5p_p3.cyclotomic_inverse_in_place();
		let result1 = f3p * &f6p * &f5p_p3;

		// step 6
		let result2 = result1.square();
		let f4_2p = f4 * &f2p;
		let mut tmp1_p3 = f0 * &f1 * &f3 * &f4_2p * &f8p;
		tmp1_p3.cyclotomic_inverse_in_place();
		let result3 = result2 * &f5 * &f0p * &tmp1_p3;

		// step 7
		let result4 = result3.square();
		let mut f7_p3 = f7;
		f7_p3.cyclotomic_inverse_in_place();
		let result5 = result4 * &f9p * &f7_p3;

		// step 8
		let result6 = result5.square();
		let f2_4p = f2 * &f4p;
		let f4_2p_5p = f4_2p * &f5p;
		let mut tmp2_p3 = f2_4p * &f3 * &f3p;
		tmp2_p3.cyclotomic_inverse_in_place();
		let result7 = result6 * &f4_2p_5p * &f6 * &f7p * &tmp2_p3;

		// step 9
		let result8 = result7.square();
		let mut tmp3_p3 = f0p * &f9p;
		tmp3_p3.cyclotomic_inverse_in_place();
		let result9 = result8 * &f0 * &f7 * &f1p * &tmp3_p3;

		// step 10
		let result10 = result9.square();
		let f6p_8p = f6p * &f8p;
		let f5_7p = f5 * &f7p;
		let mut tmp4_p3 = f6p_8p;
		tmp4_p3.cyclotomic_inverse_in_place();
		let result11 = result10 * &f5_7p * &f2p * &tmp4_p3;

		// step 11
		let result12 = result11.square();
		let f3_6 = f3 * &f6;
		let f1_7 = f1 * &f7;
		let mut tmp5_p3 = f1_7 * &f2;
		tmp5_p3.cyclotomic_inverse_in_place();
		let result13 = result12 * &f3_6 * &f9p * &tmp5_p3;

		// step 12
		let result14 = result13.square();
		let mut tmp6_p3 = f4_2p * &f5_7p * &f6p_8p;
		tmp6_p3.cyclotomic_inverse_in_place();
		let result15 = result14 * &f0 * &f0p * &f3p * &f5p * &tmp6_p3;

		// step 13
		let result16 = result15.square();
		let mut tmp7_p3 = f3_6;
		tmp7_p3.cyclotomic_inverse_in_place();
		let result17 = result16 * &f1p * &tmp7_p3;

		// step 14
		let result18 = result17.square();
		let mut tmp8_p3 = f2_4p * &f4_2p_5p * &f9p;
		tmp8_p3.cyclotomic_inverse_in_place();
		let result19 = result18 * &f1_7 * &f5_7p * &f0p * &tmp8_p3;

		result19
	}
}

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
