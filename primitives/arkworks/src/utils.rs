use crate::PairingError;
use ark_ec::{
	pairing::{MillerLoopOutput, Pairing},
	AffineRepr, Group,
};
use ark_ff::Zero;
use ark_serialize::{
	CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Validate,
};
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

pub fn serialize_iter_to_vec<T>(
	iter: impl IntoIterator<Item = T>,
) -> Result<Vec<u8>, SerializationError>
where
	T: CanonicalSerialize + Sized + Zero,
{
	let iter = iter.into_iter();
	let element_size = T::zero().uncompressed_size();
	let length: usize =
		iter.size_hint().0.try_into().map_err(|_| SerializationError::InvalidData)?;
	let mut w = Cursor::new(Vec::with_capacity(8 + element_size * length));
	length.serialize_uncompressed(&mut w)?;
	let mut length = 0u32;
	for elem in iter {
		elem.serialize_uncompressed(&mut w)?;
		length += 1;
	}
	let result = w.into_inner();
	// elem.serialize_uncompressed::<&mut &mut T>(&mut result.as_mut())?;
	Ok(result)
}

pub fn deserialize_iter_to_vec<T>(mut bytes: &[u8]) -> Result<Vec<T>, SerializationError>
where
	T: CanonicalDeserialize + Sized,
{
	let cursor = Cursor::new(bytes.to_vec());
	let length = u32::deserialize_uncompressed_unchecked(cursor.clone())?;
	let mut result = Vec::with_capacity(length as usize);
	for _ in 0..length {
		result.push(T::deserialize_uncompressed_unchecked(cursor.clone())?);
	}
	Ok(result)
}

pub fn multi_miller_loop_generic<Curve: Pairing>(
	a_vec: Vec<u8>,
	b_vec: Vec<u8>,
) -> Result<Vec<u8>, PairingError> {
	let g1: Vec<_> = deserialize_iter_to_vec::<<Curve as Pairing>::G1Affine>(&a_vec)
		.map_err(|_| PairingError::InternalPanic)?;
	let g2: Vec<_> = deserialize_iter_to_vec::<<Curve as Pairing>::G2Affine>(&b_vec)
		.map_err(|_| PairingError::InternalPanic)?;

	let result = Curve::multi_miller_loop(g1, g2);

	Ok(serialize_result(result.0))
}

pub fn final_exponentiation_generic<Curve: Pairing>(
	target: Vec<u8>,
) -> Result<Vec<u8>, PairingError> {
	let target = deserialize_argument::<<Curve as Pairing>::TargetField>(&target);

	let result = Curve::final_exponentiation(MillerLoopOutput(target));

	match result {
		Some(result) => Ok(serialize_result(result)),
		None => Err(PairingError::FinalExpInverse),
	}
}

pub fn msm_g1_generic<Curve: Pairing>(bases: Vec<u8>, scalars: Vec<u8>) -> Vec<u8> {
	let bases: Vec<_> = bases
		.chunks(<Curve as Pairing>::G1Affine::generator().serialized_size(Compress::No))
		.into_iter()
		.map(|a| deserialize_argument::<<Curve as Pairing>::G1Affine>(&a.to_vec()))
		.collect();
	let scalars: Vec<_> = scalars
		.chunks(Curve::ScalarField::zero().serialized_size(Compress::No))
		.into_iter()
		.map(|a| deserialize_argument::<Curve::ScalarField>(&a.to_vec()))
		.collect();

	let result =
		<<Curve as Pairing>::G1 as ark_ec::VariableBaseMSM>::msm(&bases, &scalars).unwrap();

	serialize_result(result)
}

pub fn msm_g2_generic<Curve: Pairing>(bases: Vec<u8>, scalars: Vec<u8>) -> Vec<u8> {
	let bases: Vec<_> = bases
		.chunks(<Curve as Pairing>::G2Affine::generator().serialized_size(Compress::No))
		.into_iter()
		.map(|a| deserialize_argument::<<Curve as Pairing>::G2Affine>(&a.to_vec()))
		.collect();
	let scalars: Vec<_> = scalars
		.chunks(Curve::ScalarField::zero().serialized_size(Compress::No))
		.into_iter()
		.map(|a| deserialize_argument::<Curve::ScalarField>(&a.to_vec()))
		.collect();

	let result =
		<<Curve as Pairing>::G2 as ark_ec::VariableBaseMSM>::msm(&bases, &scalars).unwrap();

	serialize_result(result)
}
