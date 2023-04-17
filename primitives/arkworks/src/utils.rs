use ark_ec::{
	pairing::{MillerLoopOutput, Pairing, PairingOutput},
	short_weierstrass,
	short_weierstrass::SWCurveConfig,
	twisted_edwards,
	twisted_edwards::TECurveConfig,
	CurveConfig, VariableBaseMSM,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use ark_std::{io::Cursor, vec, vec::Vec};
use codec::{Decode, Encode};

const HOST_CALL: ark_scale::Usage = ark_scale::HOST_CALL;
type ArkScale<T> = ark_scale::ArkScale<T, HOST_CALL>;

fn serialize_result(result: impl CanonicalSerialize) -> Vec<u8> {
	let mut serialized_result = vec![0u8; result.serialized_size(Compress::No)];
	let mut cursor = Cursor::new(&mut serialized_result[..]);
	result.serialize_uncompressed(&mut cursor).unwrap();
	serialized_result
}

fn deserialize_argument<Field: CanonicalDeserialize>(argument: &Vec<u8>) -> Field {
	let cursor = Cursor::new(argument);
	Field::deserialize_with_mode(cursor, Compress::No, Validate::No).unwrap()
}

/// Compute a multi miller loop through arkworks
pub fn multi_miller_loop_generic<Curve: Pairing>(g1: Vec<u8>, g2: Vec<u8>) -> Result<Vec<u8>, ()> {
	let g1 =
		<ArkScale<Vec<<Curve as Pairing>::G1Affine>> as Decode>::decode(&mut g1.clone().as_slice())
			.map_err(|_| ())?;
	let g2 =
		<ArkScale<Vec<<Curve as Pairing>::G2Affine>> as Decode>::decode(&mut g2.clone().as_slice())
			.map_err(|_| ())?;

	let result = Curve::multi_miller_loop(g1.0, g2.0).0;

	let result: ArkScale<<Curve as Pairing>::TargetField> = result.into();
	Ok(<ArkScale<<Curve as Pairing>::TargetField> as Encode>::encode(&result))
}

/// Compute a final exponentiation through arkworks
pub fn final_exponentiation_generic<Curve: Pairing>(target: Vec<u8>) -> Result<Vec<u8>, ()> {
	let target = <ArkScale<<Curve as Pairing>::TargetField> as Decode>::decode(
		&mut target.clone().as_slice(),
	)
	.map_err(|_| ())?;

	let result = Curve::final_exponentiation(MillerLoopOutput(target.0)).ok_or(())?;

	let result: ArkScale<PairingOutput<Curve>> = result.into();
	Ok(<ArkScale<PairingOutput<Curve>> as Encode>::encode(&result))
}

/// Compute a multi scalar multiplication for short_weierstrass through arkworks
pub fn msm_sw_generic<Curve: SWCurveConfig>(
	bases: Vec<u8>,
	scalars: Vec<u8>,
) -> Result<Vec<u8>, ()> {
	let bases = <ArkScale<Vec<short_weierstrass::Affine<Curve>>> as Decode>::decode(
		&mut bases.clone().as_slice(),
	)
	.map_err(|_| ())?;
	let scalars = <ArkScale<Vec<<Curve as CurveConfig>::ScalarField>> as Decode>::decode(
		&mut scalars.clone().as_slice(),
	)
	.map_err(|_| ())?;

	let result =
		<short_weierstrass::Projective<Curve> as VariableBaseMSM>::msm(&bases.0, &scalars.0)
			.map_err(|_| ())?;

	let result: ArkScale<short_weierstrass::Projective<Curve>> = result.into();
	Ok(<ArkScale<short_weierstrass::Projective<Curve>> as Encode>::encode(&result))
}

/// Compute a multi scalar mulitplication for twisted_edwards through arkworks
pub fn msm_te_generic<Curve: TECurveConfig>(
	bases: Vec<u8>,
	scalars: Vec<u8>,
) -> Result<Vec<u8>, ()> {
	let bases = <ArkScale<Vec<twisted_edwards::Affine<Curve>>> as Decode>::decode(
		&mut bases.clone().as_slice(),
	)
	.map_err(|_| ())?;
	let scalars = <ArkScale<Vec<<Curve as CurveConfig>::ScalarField>> as Decode>::decode(
		&mut scalars.clone().as_slice(),
	)
	.map_err(|_| ())?;

	let result =
		<twisted_edwards::Projective<Curve> as VariableBaseMSM>::msm(&bases.0, &scalars.0).unwrap();

	let result: ArkScale<twisted_edwards::Projective<Curve>> = result.into();
	Ok(<ArkScale<twisted_edwards::Projective<Curve>> as Encode>::encode(&result))
}

/// Compute a projective scalar multiplication on G2 through arkworks
pub fn mul_projective_generic<Group: SWCurveConfig>(
	base: Vec<u8>,
	scalar: Vec<u8>,
) -> Result<Vec<u8>, ()> {
	let base = <ArkScale<short_weierstrass::Projective<Group>> as Decode>::decode(
		&mut base.clone().as_slice(),
	)
	.map_err(|_| ())?;
	let scalar =
		<ArkScale<Vec<u64>> as Decode>::decode(&mut scalar.clone().as_slice()).map_err(|_| ())?;

	let result = <Group as SWCurveConfig>::mul_projective(&base.0, &scalar.0);

	let result: ArkScale<short_weierstrass::Projective<Group>> = result.into();
	Ok(<ArkScale<short_weierstrass::Projective<Group>> as Encode>::encode(&result))
}

/// Compute a projective scalar multiplication for twisted_edwards through arkworks
pub fn mul_projective_te_generic<Group: TECurveConfig>(
	base: Vec<u8>,
	scalar: Vec<u8>,
) -> Result<Vec<u8>, ()> {
	let base = <ArkScale<twisted_edwards::Projective<Group>> as Decode>::decode(
		&mut base.clone().as_slice(),
	)
	.map_err(|_| ())?;
	let scalar =
		<ArkScale<Vec<u64>> as Decode>::decode(&mut scalar.clone().as_slice()).map_err(|_| ())?;

	let result = <Group as TECurveConfig>::mul_projective(&base.0, &scalar.0);

	let result: ArkScale<twisted_edwards::Projective<Group>> = result.into();
	Ok(<ArkScale<twisted_edwards::Projective<Group>> as Encode>::encode(&result))
}

/// Compute a affine scalar multiplication through arkworks
pub fn mul_affine_generic<Group: SWCurveConfig>(
	base: Vec<u8>,
	scalar: Vec<u8>,
) -> Result<Vec<u8>, ()> {
	let base = <ArkScale<short_weierstrass::Affine<Group>> as Decode>::decode(
		&mut base.clone().as_slice(),
	)
	.map_err(|_| ())?;
	let scalar =
		<ArkScale<Vec<u64>> as Decode>::decode(&mut scalar.clone().as_slice()).map_err(|_| ())?;

	let result = <Group as SWCurveConfig>::mul_affine(&base.0, &scalar.0);

	let result: ArkScale<short_weierstrass::Projective<Group>> = result.into();
	Ok(<ArkScale<short_weierstrass::Projective<Group>> as Encode>::encode(&result))
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_affine_te_generic<Group: TECurveConfig>(
	base: Vec<u8>,
	scalar: Vec<u8>,
) -> Result<Vec<u8>, ()> {
	let base =
		<ArkScale<twisted_edwards::Affine<Group>> as Decode>::decode(&mut base.clone().as_slice())
			.map_err(|_| ())?;
	let scalar =
		<ArkScale<Vec<u64>> as Decode>::decode(&mut scalar.clone().as_slice()).map_err(|_| ())?;

	let result = <Group as TECurveConfig>::mul_affine(&base.0, &scalar.0);

	let result: ArkScale<twisted_edwards::Projective<Group>> = result.into();
	Ok(<ArkScale<twisted_edwards::Projective<Group>> as Encode>::encode(&result))
}
