use ark_ff::{Field, MontFp, Zero};
use ark_models::models::{
	short_weierstrass::{Affine as SWAffine, Projective, SWCurveConfig},
	twisted_edwards::{
		Affine as TEAffine, MontCurveConfig, Projective as TEProjective, TECurveConfig,
	},
	CurveConfig,
};
use ark_serialize::{CanonicalSerialize, Compress, Validate};
use ark_std::{io::Cursor, vec, vec::Vec};
use core::ops::Neg;

use crate::{Fq, Fr};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
	type BaseField = Fq;
	type ScalarField = Fr;

	/// COFACTOR = (x - 1)^2 / 3  = 30631250834960419227450344600217059328
	const COFACTOR: &'static [u64] = &[0x0, 0x170b5d4430000000];

	/// COFACTOR_INV = COFACTOR^{-1} mod r
	/// = 5285428838741532253824584287042945485047145357130994810877
	const COFACTOR_INV: Fr = MontFp!("5285428838741532253824584287042945485047145357130994810877");
}

impl SWCurveConfig for Config {
	/// COEFF_A = 0
	const COEFF_A: Fq = Fq::ZERO;

	/// COEFF_B = 1
	const COEFF_B: Fq = Fq::ONE;

	/// AFFINE_GENERATOR_COEFFS = (G1_GENERATOR_X, G1_GENERATOR_Y)
	const GENERATOR: G1SWAffine = G1SWAffine::new_unchecked(G1_GENERATOR_X, G1_GENERATOR_Y);

	#[inline(always)]
	fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
		Self::BaseField::zero()
	}

	fn msm(
		bases: &[SWAffine<Self>],
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
		let result = sp_io::crypto::bls12_377_msm_g1(bases, scalars);
		let cursor = Cursor::new(&result[..]);
		let result =
			<Config as SWCurveConfig>::deserialize_with_mode(cursor, Compress::Yes, Validate::No)
				.unwrap();
		Ok(result.into())
	}

	fn mul_projective(base: &Projective<Self>, scalar: &[u64]) -> Projective<Self> {
		let mut serialized_base = vec![0; base.serialized_size(Compress::Yes)];
		let mut cursor = Cursor::new(&mut serialized_base[..]);
		base.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();

		let mut serialized_scalar = vec![0; scalar.serialized_size(Compress::Yes)];
		let mut cursor = Cursor::new(&mut serialized_scalar[..]);
		scalar.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();

		let result = sp_io::crypto::bls12_377_mul_projective_g1(serialized_base, serialized_scalar);

		let cursor = Cursor::new(&result[..]);

		let result =
			<Config as SWCurveConfig>::deserialize_with_mode(cursor, Compress::Yes, Validate::No)
				.unwrap();
		result.into()
	}

    fn mul_affine(base: &SWAffine<Self>, scalar: &[u64]) -> Projective<Self> {
		let mut serialized_base = vec![0; base.serialized_size(Compress::Yes)];
		let mut cursor = Cursor::new(&mut serialized_base[..]);
		base.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();

		let mut serialized_scalar = vec![0; scalar.serialized_size(Compress::Yes)];
		let mut cursor = Cursor::new(&mut serialized_scalar[..]);
		scalar.serialize_with_mode(&mut cursor, Compress::Yes).unwrap();

		let serialized_result =
			sp_io::crypto::bls12_377_mul_affine_g1(serialized_base, serialized_scalar);

		let cursor = Cursor::new(&serialized_result[..]);

		let result = <Config as SWCurveConfig>::deserialize_with_mode(cursor, Compress::Yes, Validate::No).unwrap();
		result.into()
	}
}

pub type G1SWAffine = SWAffine<Config>;
pub type G1TEAffine = TEAffine<Config>;
pub type G1TEProjective = TEProjective<Config>;

/// Bls12_377::G1 also has a twisted Edwards form.
/// It can be obtained via the following script, implementing
/// 1. SW -> Montgomery -> TE1 transformation: <https://en.wikipedia.org/wiki/Montgomery_curve>
/// 2. TE1 -> TE2 normalization (enforcing `a = -1`)
/// ``` sage
/// # modulus
/// p = 0x1ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001
/// Fp = Zmod(p)
///
/// #####################################################
/// # Weierstrass curve: y² = x³ + A * x + B
/// #####################################################
/// # curve y^2 = x^3 + 1
/// WA = Fp(0)
/// WB = Fp(1)
///
/// #####################################################
/// # Montgomery curve: By² = x³ + A * x² + x
/// #####################################################
/// # root for x^3 + 1 = 0
/// alpha = -1
/// # s = 1 / (sqrt(3alpha^2 + a))
/// s = 1/(Fp(3).sqrt())
///
/// # MA = 3 * alpha * s
/// MA = Fp(228097355113300204138531148905234651262148041026195375645000724271212049151994375092458297304264351187709081232384)
/// # MB = s
/// MB = Fp(10189023633222963290707194929886294091415157242906428298294512798502806398782149227503530278436336312243746741931)
///
/// # #####################################################
/// # # Twisted Edwards curve 1: a * x² + y² = 1 + d * x² * y²
/// # #####################################################
/// # We first convert to TE form obtaining a curve with a != -1, and then
/// # apply a transformation to obtain a TE curve with a = -1.
/// # a = (MA+2)/MB
/// TE1a = Fp(61134141799337779744243169579317764548490943457438569789767076791016838392692895365021181670618017873462480451583)
/// # b = (MA-2)/MB
/// TE1d = Fp(197530284213631314266409564115575768987902569297476090750117185875703629955647927409947706468955342250977841006588)
///
/// # #####################################################
/// # # Twisted Edwards curve 2: a * x² + y² = 1 + d * x² * y²
/// # #####################################################
/// # a = -1
/// TE2a = Fp(-1)
/// # b = -TE1d/TE1a
/// TE2d = Fp(122268283598675559488486339158635529096981886914877139579534153582033676785385790730042363341236035746924960903179)
/// ```
impl TECurveConfig for Config {
	/// COEFF_A = -1
	const COEFF_A: Fq = MontFp!("-1");

	/// COEFF_D = 122268283598675559488486339158635529096981886914877139579534153582033676785385790730042363341236035746924960903179 mod q
	const COEFF_D: Fq = MontFp!("122268283598675559488486339158635529096981886914877139579534153582033676785385790730042363341236035746924960903179");

	/// AFFINE_GENERATOR_COEFFS = (GENERATOR_X, GENERATOR_Y)
	const GENERATOR: G1TEAffine = G1TEAffine::new_unchecked(TE_GENERATOR_X, TE_GENERATOR_Y);

	type MontCurveConfig = Config;

	/// Multiplication by `a` is multiply by `-1`.
	#[inline(always)]
	fn mul_by_a(elem: Self::BaseField) -> Self::BaseField {
		elem.neg()
	}
}

// BLS12-377::G1 also has a Montgomery form.
// BLS12-377::G1 also has a twisted Edwards form.
// It can be obtained via the following script, implementing
// SW -> Montgomery transformation: <https://en.wikipedia.org/wiki/Montgomery_curve>
// ``` sage
// # modulus
// p=0x1ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001
// Fp=Zmod(p)
//
// #####################################################
// # Weierstrass curve: y² = x³ + A * x + B
// #####################################################
// # curve y^2 = x^3 + 1
// WA=Fp(0)
// WB=Fp(1)
//
// #####################################################
// # Montgomery curve: By² = x³ + A * x² + x
// #####################################################
// # root for x^3 + 1 = 0
// alpha = -1
// # s = 1 / (sqrt(3alpha^2 + a))
// s = 1/(Fp(3).sqrt())
//
// # MA = 3 * alpha * s
// MA=Fp(228097355113300204138531148905234651262148041026195375645000724271212049151994375092458297304264351187709081232384)
// # MB = s
// MB=Fp(10189023633222963290707194929886294091415157242906428298294512798502806398782149227503530278436336312243746741931)
// ```
impl MontCurveConfig for Config {
	/// COEFF_A = 228097355113300204138531148905234651262148041026195375645000724271212049151994375092458297304264351187709081232384
	const COEFF_A: Fq = MontFp!("228097355113300204138531148905234651262148041026195375645000724271212049151994375092458297304264351187709081232384");

	/// COEFF_B = 10189023633222963290707194929886294091415157242906428298294512798502806398782149227503530278436336312243746741931
	const COEFF_B: Fq = MontFp!("10189023633222963290707194929886294091415157242906428298294512798502806398782149227503530278436336312243746741931");

	type TECurveConfig = Config;
}

/// G1_GENERATOR_X =
/// 81937999373150964239938255573465948239988671502647976594219695644855304257327692006745978603320413799295628339695
pub const G1_GENERATOR_X: Fq = MontFp!("81937999373150964239938255573465948239988671502647976594219695644855304257327692006745978603320413799295628339695");

/// G1_GENERATOR_Y =
/// 241266749859715473739788878240585681733927191168601896383759122102112907357779751001206799952863815012735208165030
pub const G1_GENERATOR_Y: Fq = MontFp!("241266749859715473739788878240585681733927191168601896383759122102112907357779751001206799952863815012735208165030");

// The generator for twisted Edward form is the same SW generator converted into
// the normalized TE form (TE2).
//``` sage
// # following scripts in previous section
// #####################################################
// # Weierstrass curve generator
// #####################################################
// Wx = Fp(81937999373150964239938255573465948239988671502647976594219695644855304257327692006745978603320413799295628339695)
// Wy = Fp(241266749859715473739788878240585681733927191168601896383759122102112907357779751001206799952863815012735208165030)
//
// assert(Wy^2 - Wx^3 - WA * Wx - WB == 0)
//
// #####################################################
// # Montgomery curve generator
// #####################################################
// # x = s * (x - alpha)
// Mx = Fp(251803586774461569862800610331871502335378228972505599912537082323947581271784390797244487924068052270360793200630)
// # y = s * y
// My = Fp(77739247071951651095607889637653357561348174979132042929587539214321586851215673796661346812932566642719051699820)
//
// assert(MB * My^2 == Mx^3+ MA * Mx^2 + Mx)
//
// # #####################################################
// # # Twisted Edwards curve 1 generator
// # #####################################################
// # x = Mx/My
// TE1x = Fp(82241236807150726090333472814441006963902378430536027612759193445733851062772474760677400112551677454953925168208)
// # y = (Mx - 1)/(Mx+1)
// TE1y = Fp(6177051365529633638563236407038680211609544222665285371549726196884440490905471891908272386851767077598415378235)
//
// assert( TE1a * TE1x^2 + TE1y^2 == 1 + TE1d * TE1x^2 * TE1y^2 )
//
//
// # #####################################################
// # # Twisted Edwards curve 2 generator
// # #####################################################
// beta = (-TE1a).sqrt()
// # x = TE1x * sqrt(-TE1a)
// TE2x = Fp(71222569531709137229370268896323705690285216175189308202338047559628438110820800641278662592954630774340654489393)
// # y = TE1y
// TE2y = Fp(6177051365529633638563236407038680211609544222665285371549726196884440490905471891908272386851767077598415378235)
//
// assert( TE2a * TE2x^2 + TE2y^2 == 1 + TE2d * TE2x^2 * TE2y^2 )
// ```
/// TE_GENERATOR_X =
/// 71222569531709137229370268896323705690285216175189308202338047559628438110820800641278662592954630774340654489393
pub const TE_GENERATOR_X: Fq = MontFp!("71222569531709137229370268896323705690285216175189308202338047559628438110820800641278662592954630774340654489393");

/// TE_GENERATOR_Y =
/// 6177051365529633638563236407038680211609544222665285371549726196884440490905471891908272386851767077598415378235
pub const TE_GENERATOR_Y: Fq = MontFp!("6177051365529633638563236407038680211609544222665285371549726196884440490905471891908272386851767077598415378235");
