use ark_ec::{
	pairing::{MillerLoopOutput, Pairing},
	short_weierstrass,
	short_weierstrass::SWCurveConfig,
	twisted_edwards,
	twisted_edwards::TECurveConfig,
	CurveConfig, VariableBaseMSM,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use ark_std::{io::Cursor, vec, vec::Vec};

pub fn serialize_result(result: impl CanonicalSerialize) -> Vec<u8> {
	let mut serialized_result = vec![0u8; result.serialized_size(Compress::No)];
	let mut cursor = Cursor::new(&mut serialized_result[..]);
	result.serialize_uncompressed(&mut cursor).unwrap();
	serialized_result
}

pub fn deserialize_argument<Field: CanonicalDeserialize>(argument: &Vec<u8>) -> Field {
	let cursor = Cursor::new(argument);
	Field::deserialize_with_mode(cursor, Compress::No, Validate::No).unwrap()
}

pub fn multi_miller_loop_generic<Curve: Pairing>(
	a_vec: Vec<Vec<u8>>,
	b_vec: Vec<Vec<u8>>,
) -> Result<Vec<u8>, ()> {
	let g1: Vec<_> = a_vec
		.iter()
		.map(|elem| deserialize_argument::<<Curve as Pairing>::G1Affine>(elem))
		.collect();
	let g2: Vec<_> = b_vec
		.iter()
		.map(|elem| deserialize_argument::<<Curve as Pairing>::G2Affine>(elem))
		.collect();

	let result = Curve::multi_miller_loop(g1, g2);

	Ok(serialize_result(result.0))
}

pub fn final_exponentiation_generic<Curve: Pairing>(target: Vec<u8>) -> Result<Vec<u8>, ()> {
	let target = deserialize_argument::<<Curve as Pairing>::TargetField>(&target);

	let result = Curve::final_exponentiation(MillerLoopOutput(target));

	match result {
		Some(result) => Ok(serialize_result(result)),
		None => Err(()),
	}
}

pub fn msm_sw_generic<Curve: SWCurveConfig>(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	let bases: Vec<_> = bases
		.iter()
		.map(|a| deserialize_argument::<short_weierstrass::Affine<Curve>>(a))
		.collect();
	let scalars: Vec<_> = scalars
		.iter()
		.map(|a| deserialize_argument::<<Curve as CurveConfig>::ScalarField>(a))
		.collect();

	let result =
		<short_weierstrass::Projective<Curve> as VariableBaseMSM>::msm(&bases, &scalars).unwrap();

	serialize_result(result)
}

pub fn msm_te_generic<Curve: TECurveConfig>(bases: Vec<Vec<u8>>, scalars: Vec<Vec<u8>>) -> Vec<u8> {
	let bases: Vec<_> = bases
		.iter()
		.map(|a| deserialize_argument::<twisted_edwards::Affine<Curve>>(a))
		.collect();
	let scalars: Vec<_> = scalars
		.iter()
		.map(|a| deserialize_argument::<<Curve as CurveConfig>::ScalarField>(a))
		.collect();

	let result =
		<twisted_edwards::Projective<Curve> as VariableBaseMSM>::msm(&bases, &scalars).unwrap();

	serialize_result(result)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_projective_generic<Group: SWCurveConfig>(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let base = deserialize_argument::<short_weierstrass::Projective<Group>>(&base);
	let scalar = deserialize_argument::<Vec<u64>>(&scalar);

	let result = <Group as SWCurveConfig>::mul_projective(&base, &scalar);

	serialize_result(result)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_projective_te_generic<Group: TECurveConfig>(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let base = deserialize_argument::<twisted_edwards::Projective<Group>>(&base);
	let scalar = deserialize_argument::<Vec<u64>>(&scalar);

	let result = <Group as TECurveConfig>::mul_projective(&base, &scalar);

	serialize_result(result)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_affine_generic<Group: SWCurveConfig>(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let base = deserialize_argument::<short_weierstrass::Affine<Group>>(&base);
	let scalar = deserialize_argument::<Vec<u64>>(&scalar);

	let result = <Group as SWCurveConfig>::mul_affine(&base, &scalar);

	serialize_result(result)
}

/// Compute a scalar multiplication on G2 through arkworks
pub fn mul_affine_te_generic<Group: TECurveConfig>(base: Vec<u8>, scalar: Vec<u8>) -> Vec<u8> {
	let base = deserialize_argument::<twisted_edwards::Affine<Group>>(&base);
	let scalar = deserialize_argument::<Vec<u64>>(&scalar);

	let result = <Group as TECurveConfig>::mul_affine(&base, &scalar);

	serialize_result(result)
}
