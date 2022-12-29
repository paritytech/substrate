use ark_ff::{Field, MontFp};
use ark_models::{
	models::{short_weierstrass::SWCurveConfig, CurveConfig},
	short_weierstrass::{Affine, Projective},
};
use ark_serialize::{CanonicalSerialize, Compress, Validate};
use ark_std::{io::Cursor, vec, vec::Vec};

use crate::{Fq, Fr};

pub type G1Affine = Affine<Config>;
pub type G1Projective = Projective<Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
	type BaseField = Fq;
	type ScalarField = Fr;

	/// COFACTOR =
	/// 26642435879335816683987677701488073867751118270052650655942102502312977592501693353047140953112195348280268661194876
    #[rustfmt::skip]
	const COFACTOR: &'static [u64] = &[
        0x3de580000000007c,
        0x832ba4061000003b,
        0xc61c554757551c0c,
        0xc856a0853c9db94c,
        0x2c77d5ac34cb12ef,
        0xad1972339049ce76,
    ];

	/// COFACTOR^(-1) mod r =
	/// 91141326767669940707819291241958318717982251277713150053234367522357946997763584490607453720072232540829942217804
	const COFACTOR_INV: Fr = MontFp!("91141326767669940707819291241958318717982251277713150053234367522357946997763584490607453720072232540829942217804");
}

impl SWCurveConfig for Config {
	/// COEFF_A = 0
	const COEFF_A: Fq = Fq::ZERO;

	/// COEFF_B = -1
	const COEFF_B: Fq = MontFp!("-1");

	/// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
	const GENERATOR: G1Affine = G1Affine::new_unchecked(G1_GENERATOR_X, G1_GENERATOR_Y);
	#[inline(always)]
	fn mul_by_a(_elem: Self::BaseField) -> Self::BaseField {
		use ark_ff::Zero;
		Self::BaseField::zero()
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
		let result = sp_io::crypto::bw6_761_msm_g1(bases, scalars);
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

		let result = sp_io::crypto::bw6_761_mul_projective_g1(serialized_base, serialized_scalar);

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
			sp_io::crypto::bw6_761_mul_affine_g1(serialized_base, serialized_scalar);

		let cursor = Cursor::new(&serialized_result[..]);

		let result = Self::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
		result.into()
	}
}

/// G1_GENERATOR_X =
/// 6238772257594679368032145693622812838779005809760824733138787810501188623461307351759238099287535516224314149266511977132140828635950940021790489507611754366317801811090811367945064510304504157188661901055903167026722666149426237
pub const G1_GENERATOR_X: Fq = MontFp!("6238772257594679368032145693622812838779005809760824733138787810501188623461307351759238099287535516224314149266511977132140828635950940021790489507611754366317801811090811367945064510304504157188661901055903167026722666149426237");

/// G1_GENERATOR_Y =
/// 2101735126520897423911504562215834951148127555913367997162789335052900271653517958562461315794228241561913734371411178226936527683203879553093934185950470971848972085321797958124416462268292467002957525517188485984766314758624099
pub const G1_GENERATOR_Y: Fq = MontFp!("2101735126520897423911504562215834951148127555913367997162789335052900271653517958562461315794228241561913734371411178226936527683203879553093934185950470971848972085321797958124416462268292467002957525517188485984766314758624099");
