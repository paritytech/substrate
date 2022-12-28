use ark_ff::Fp12;
use ark_models::{
	bls12,
	bls12::{Bls12, Bls12Config, G1Prepared, G2Prepared, TwistType},
	pairing::{MillerLoopOutput, Pairing, PairingOutput},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use ark_std::{io::Cursor, vec, vec::Vec};

use crate::*;

pub mod g1;
pub mod g2;

#[cfg(test)]
mod tests;

pub struct Config;

impl Bls12Config for Config {
	const X: &'static [u64] = &[0x8508c00000000001];
	/// `x` is positive.
	const X_IS_NEGATIVE: bool = false;
	const TWIST_TYPE: TwistType = TwistType::D;
	type Fp = Fq;
	type Fp2Config = Fq2Config;
	type Fp6Config = Fq6Config;
	type Fp12Config = Fq12Config;
	type G1Config = g1::Config;
	type G2Config = g2::Config;

	fn multi_miller_loop(
		a: impl IntoIterator<Item = impl Into<G1Prepared<Self>>>,
		b: impl IntoIterator<Item = impl Into<G2Prepared<Self>>>,
	) -> MillerLoopOutput<Bls12<Self>> {
		let a: Vec<Vec<u8>> = a
			.into_iter()
			.map(|elem| {
				let elem: <Bls12<Self> as Pairing>::G1Prepared = elem.into();
				let mut serialized = vec![0; elem.serialized_size(Compress::Yes)];
				let mut cursor = Cursor::new(&mut serialized[..]);
				elem.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
				serialized
			})
			.collect();
		let b = b
			.into_iter()
			.map(|elem| {
				let elem: <Bls12<Self> as Pairing>::G2Prepared = elem.into();
				let mut serialized = vec![0u8; elem.serialized_size(Compress::Yes)];
				let mut cursor = Cursor::new(&mut serialized[..]);
				elem.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
				serialized
			})
			.collect();

		let res = sp_io::crypto::bls12_377_multi_miller_loop(a, b);
		let cursor = Cursor::new(&res[..]);
		let f: <Bls12<Self> as Pairing>::TargetField =
			Fp12::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
		MillerLoopOutput(f)
	}

	fn final_exponentiation(
		f: MillerLoopOutput<Bls12<Self>>,
	) -> Option<PairingOutput<Bls12<Self>>> {
		let mut out: [u8; 576] = [0; 576];
		let mut cursor = Cursor::new(&mut out[..]);
		f.0.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();

		let res = sp_io::crypto::bls12_377_final_exponentiation(&out);

		let cursor = Cursor::new(&res[..]);
		let res = PairingOutput::<Bls12<Self>>::deserialize_with_mode(
			cursor,
			Compress::Yes,
			Validate::No,
		)
		.unwrap();

		Some(res)
	}
}

pub type Bls12_377 = Bls12<Config>;

pub type G1Affine = bls12::G1Affine<Config>;
pub type G1Projective = bls12::G1Projective<Config>;
pub type G2Affine = bls12::G2Affine<Config>;
pub type G2Projective = bls12::G2Projective<Config>;

pub use g1::{G1TEAffine, G1TEProjective};
