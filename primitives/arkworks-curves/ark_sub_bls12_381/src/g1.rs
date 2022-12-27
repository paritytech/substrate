use crate::*;
use ark_bls12_381::{Fq, Fq2, Fr};
use ark_ff::{Field, MontFp, PrimeField, Zero};
use ark_models::{
	bls12,
	bls12::Bls12Config,
	models::CurveConfig,
	short_weierstrass::{Affine, Projective, SWCurveConfig},
	AffineRepr, Group,
};
use ark_serialize::{Compress, SerializationError};
use ark_std::{ops::Neg, One};

use crate::util::{
	read_g1_compressed, read_g1_uncompressed, serialize_fq, EncodingFlags, G1_SERIALIZED_SIZE,
};

pub type G1Affine = bls12::G1Affine<crate::Config>;
pub type G1Projective = bls12::G1Projective<crate::Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
	type BaseField = Fq;
	type ScalarField = Fr;

	/// COFACTOR = (x - 1)^2 / 3  = 76329603384216526031706109802092473003
	const COFACTOR: &'static [u64] = &[0x8c00aaab0000aaab, 0x396c8c005555e156];

	/// COFACTOR_INV = COFACTOR^{-1} mod r
	/// = 52435875175126190458656871551744051925719901746859129887267498875565241663483
	const COFACTOR_INV: Fr =
		MontFp!("52435875175126190458656871551744051925719901746859129887267498875565241663483");
}

impl SWCurveConfig for Config {
	/// COEFF_A = 0
	const COEFF_A: Fq = Fq::ZERO;

	/// COEFF_B = 4
	const COEFF_B: Fq = MontFp!("4");

	/// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
	const GENERATOR: G1Affine = G1Affine::new_unchecked(G1_GENERATOR_X, G1_GENERATOR_Y);

	#[inline(always)]
	fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
		Self::BaseField::zero()
	}

	#[inline]
	fn is_in_correct_subgroup_assuming_on_curve(p: &G1Affine) -> bool {
		// Algorithm from Section 6 of https://eprint.iacr.org/2021/1130.
		//
		// Check that endomorphism_p(P) == -[X^2]P

		// An early-out optimization described in Section 6.
		// If uP == P but P != point of infinity, then the point is not in the right
		// subgroup.
		let x_times_p = p.mul_bigint(crate::Config::X);
		if x_times_p.eq(p) && !p.infinity {
			return false
		}

		let minus_x_squared_times_p = x_times_p.mul_bigint(crate::Config::X).neg();
		let endomorphism_p = endomorphism(p);
		minus_x_squared_times_p.eq(&endomorphism_p)
	}

	#[inline]
	fn clear_cofactor(p: &G1Affine) -> G1Affine {
		// Using the effective cofactor, as explained in
		// Section 5 of https://eprint.iacr.org/2019/403.pdf.
		//
		// It is enough to multiply by (1 - x), instead of (x - 1)^2 / 3
		let h_eff = one_minus_x().into_bigint();
		Config::mul_affine(&p, h_eff.as_ref()).into()
	}

	fn deserialize_with_mode<R: ark_serialize::Read>(
		mut reader: R,
		compress: ark_serialize::Compress,
		validate: ark_serialize::Validate,
	) -> Result<Affine<Self>, ark_serialize::SerializationError> {
		let p = if compress == ark_serialize::Compress::Yes {
			read_g1_compressed(&mut reader)?
		} else {
			read_g1_uncompressed(&mut reader)?
		};

		if validate == ark_serialize::Validate::Yes && !p.is_in_correct_subgroup_assuming_on_curve()
		{
			return Err(SerializationError::InvalidData)
		}
		Ok(p)
	}

	fn serialize_with_mode<W: ark_serialize::Write>(
		item: &Affine<Self>,
		mut writer: W,
		compress: ark_serialize::Compress,
	) -> Result<(), SerializationError> {
		let encoding = EncodingFlags {
			is_compressed: compress == ark_serialize::Compress::Yes,
			is_infinity: item.is_zero(),
			is_lexographically_largest: item.y > -item.y,
		};
		let mut p = *item;
		if encoding.is_infinity {
			p = G1Affine::zero();
		}
		// need to access the field struct `x` directly, otherwise we get None from xy()
		// method
		let x_bytes = serialize_fq(p.x);
		if encoding.is_compressed {
			let mut bytes: [u8; G1_SERIALIZED_SIZE] = x_bytes;

			encoding.encode_flags(&mut bytes);
			writer.write_all(&bytes)?;
		} else {
			let mut bytes = [0u8; 2 * G1_SERIALIZED_SIZE];
			bytes[0..G1_SERIALIZED_SIZE].copy_from_slice(&x_bytes[..]);
			bytes[G1_SERIALIZED_SIZE..].copy_from_slice(&serialize_fq(p.y)[..]);

			encoding.encode_flags(&mut bytes);
			writer.write_all(&bytes)?;
		};

		Ok(())
	}

	fn serialized_size(compress: Compress) -> usize {
		if compress == Compress::Yes {
			G1_SERIALIZED_SIZE
		} else {
			G1_SERIALIZED_SIZE * 2
		}
	}

	fn msm(
		bases: &[Affine<Self>],
		scalars: &[<Self as CurveConfig>::ScalarField],
	) -> Result<Projective<Self>, usize> {
		let bases: Vec<Vec<u8>> = bases
			.into_iter()
			.map(|elem| {
				let mut serialized = vec![0; elem.serialized_size(Compress::Yes)];
				let mut cursor = Cursor::new(&mut serialized[..]);
				elem.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
				serialized
			})
			.collect();
		let scalars: Vec<Vec<u8>> = scalars
			.into_iter()
			.map(|elem| {
				let mut serialized = vec![0; elem.serialized_size(Compress::Yes)];
				let mut cursor = Cursor::new(&mut serialized[..]);
				elem.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();
				serialized
			})
			.collect();
		let result = sp_io::crypto::bls12_381_msm_g1(bases, scalars);
		let cursor = Cursor::new(&result[..]);
		let result = Self::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
		Ok(result.into())
	}

	fn mul_projective(base: &Projective<Self>, scalar: &[u64]) -> Projective<Self> {
		let mut serialized_base = vec![0; base.serialized_size(Compress::Yes)];
		let mut cursor = Cursor::new(&mut serialized_base[..]);
		base.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();

		let mut serialized_scalar = vec![0; scalar.serialized_size(Compress::Yes)];
		let mut cursor = Cursor::new(&mut serialized_scalar[..]);
		scalar.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();

		let result = sp_io::crypto::bls12_381_mul_projective_g1(serialized_base, serialized_scalar);

		let cursor = Cursor::new(&result[..]);

		let result = Self::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
		result.into()
	}

	fn mul_affine(base: &Affine<Self>, scalar: &[u64]) -> Projective<Self> {
		let mut serialized_base = vec![0; base.serialized_size(Compress::Yes)];
		let mut cursor = Cursor::new(&mut serialized_base[..]);
		base.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();

		let mut serialized_scalar = vec![0; scalar.serialized_size(Compress::Yes)];
		let mut cursor = Cursor::new(&mut serialized_scalar[..]);
		scalar.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();

		let serialized_result =
			sp_io::crypto::bls12_381_mul_affine_g1(serialized_base, serialized_scalar);

		let cursor = Cursor::new(&serialized_result[..]);

		let result = Self::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
		result.into()
	}
}

fn one_minus_x() -> Fr {
	const X: Fr = Fr::from_sign_and_limbs(!crate::Config::X_IS_NEGATIVE, crate::Config::X);
	Fr::one() - X
}

/// G1_GENERATOR_X =
/// 3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507
pub const G1_GENERATOR_X: Fq = MontFp!("3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507");

/// G1_GENERATOR_Y =
/// 1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569
pub const G1_GENERATOR_Y: Fq = MontFp!("1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569");

/// BETA is a non-trivial cubic root of unity in Fq.
pub const BETA: Fq = MontFp!("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350");

pub fn endomorphism(p: &Affine<Config>) -> Affine<Config> {
	// Endomorphism of the points on the curve.
	// endomorphism_p(x,y) = (BETA * x, y)
	// where BETA is a non-trivial cubic root of unity in Fq.
	let mut res = (*p).clone();
	res.x *= BETA;
	res
}

#[cfg(test)]
mod test {

	use super::*;
	use ark_std::{rand::Rng, UniformRand};

	fn sample_unchecked() -> Affine<g1::Config> {
		let mut rng = ark_std::test_rng();
		loop {
			let x = Fq::rand(&mut rng);
			let greatest = rng.gen();

			if let Some(p) = Affine::get_point_from_x_unchecked(x, greatest) {
				return p
			}
		}
	}

	#[test]
	fn test_cofactor_clearing() {
		const SAMPLES: usize = 100;
		for _ in 0..SAMPLES {
			let p: Affine<g1::Config> = sample_unchecked();
			let p = p.clear_cofactor();
			assert!(p.is_on_curve());
			assert!(p.is_in_correct_subgroup_assuming_on_curve());
		}
	}
}
