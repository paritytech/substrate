use ark_ff::{Field, MontFp};
use ark_models::{
	models::{short_weierstrass::SWCurveConfig, CurveConfig},
	short_weierstrass::{Affine, Projective},
};
use ark_serialize::{CanonicalSerialize, Compress, Validate};
use ark_std::{io::Cursor, vec, vec::Vec};

use crate::{Fq, Fr};

pub type G2Affine = Affine<Config>;
pub type G2Projective = Projective<Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
	type BaseField = Fq;
	type ScalarField = Fr;

	/// COFACTOR =
	/// 26642435879335816683987677701488073867751118270052650655942102502312977592501693353047140953112195348280268661194869
    #[rustfmt::skip]
	const COFACTOR: &'static [u64] = &[
        0x3de5800000000075,
        0x832ba4061000003b,
        0xc61c554757551c0c,
        0xc856a0853c9db94c,
        0x2c77d5ac34cb12ef,
        0xad1972339049ce76,
    ];

	/// COFACTOR^(-1) mod r =
	/// 214911522365886453591244899095480747723790054550866810551297776298664428889000553861210287833206024638187939842124
	const COFACTOR_INV: Fr = MontFp!("214911522365886453591244899095480747723790054550866810551297776298664428889000553861210287833206024638187939842124");
}

impl SWCurveConfig for Config {
	/// COEFF_A = 0
	const COEFF_A: Fq = Fq::ZERO;

	/// COEFF_B = 4
	const COEFF_B: Fq = MontFp!("4");

	/// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
	const GENERATOR: G2Affine = G2Affine::new_unchecked(G2_GENERATOR_X, G2_GENERATOR_Y);

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
		let result = sp_io::crypto::bw6_761_msm_g2(bases, scalars);
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

		let result = sp_io::crypto::bw6_761_mul_projective_g2(serialized_base, serialized_scalar);

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
			sp_io::crypto::bw6_761_mul_affine_g2(serialized_base, serialized_scalar);

		let cursor = Cursor::new(&serialized_result[..]);

		let result = Self::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
		result.into()
	}
}

/// G2_GENERATOR_X =
///  6445332910596979336035888152774071626898886139774101364933948236926875073754470830732273879639675437155036544153105017729592600560631678554299562762294743927912429096636156401171909259073181112518725201388196280039960074422214428
pub const G2_GENERATOR_X: Fq = MontFp!("6445332910596979336035888152774071626898886139774101364933948236926875073754470830732273879639675437155036544153105017729592600560631678554299562762294743927912429096636156401171909259073181112518725201388196280039960074422214428");

/// G2_GENERATOR_Y =
/// 562923658089539719386922163444547387757586534741080263946953401595155211934630598999300396317104182598044793758153214972605680357108252243146746187917218885078195819486220416605630144001533548163105316661692978285266378674355041
pub const G2_GENERATOR_Y: Fq = MontFp!("562923658089539719386922163444547387757586534741080263946953401595155211934630598999300396317104182598044793758153214972605680357108252243146746187917218885078195819486220416605630144001533548163105316661692978285266378674355041");
