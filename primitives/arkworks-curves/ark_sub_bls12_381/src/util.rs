use ark_ec::{short_weierstrass::Affine, AffineRepr};
use ark_ff::{BigInteger384, PrimeField};
use ark_serialize::SerializationError;

use crate::{g1::Config as G1Config, g2::Config as G2Config, G1Affine, G2Affine};
use ark_bls12_381::{Fq, Fq2};

pub const G1_SERIALIZED_SIZE: usize = 48;
pub const G2_SERIALIZED_SIZE: usize = 96;

pub struct EncodingFlags {
	pub is_compressed: bool,
	pub is_infinity: bool,
	pub is_lexographically_largest: bool,
}

impl EncodingFlags {
	pub fn get_flags(bytes: &[u8]) -> Self {
		let compression_flag_set = (bytes[0] >> 7) & 1;
		let infinity_flag_set = (bytes[0] >> 6) & 1;
		let sort_flag_set = (bytes[0] >> 5) & 1;

		Self {
			is_compressed: compression_flag_set == 1,
			is_infinity: infinity_flag_set == 1,
			is_lexographically_largest: sort_flag_set == 1,
		}
	}
	pub fn encode_flags(&self, bytes: &mut [u8]) {
		if self.is_compressed {
			bytes[0] |= 1 << 7;
		}

		if self.is_infinity {
			bytes[0] |= 1 << 6;
		}

		if self.is_compressed && !self.is_infinity && self.is_lexographically_largest {
			bytes[0] |= 1 << 5;
		}
	}
}

pub(crate) fn deserialize_fq(bytes: [u8; 48]) -> Option<Fq> {
	let mut tmp = BigInteger384::new([0, 0, 0, 0, 0, 0]);

	// Note: The following unwraps are if the compiler cannot convert
	// the byte slice into [u8;8], we know this is infallible since we
	// are providing the indices at compile time and bytes has a fixed size
	tmp.0[5] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[0..8]).unwrap());
	tmp.0[4] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[8..16]).unwrap());
	tmp.0[3] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[16..24]).unwrap());
	tmp.0[2] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[24..32]).unwrap());
	tmp.0[1] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[32..40]).unwrap());
	tmp.0[0] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[40..48]).unwrap());

	Fq::from_bigint(tmp)
}

pub(crate) fn serialize_fq(field: Fq) -> [u8; 48] {
	let mut result = [0u8; 48];

	let rep = field.into_bigint();

	result[0..8].copy_from_slice(&rep.0[5].to_be_bytes());
	result[8..16].copy_from_slice(&rep.0[4].to_be_bytes());
	result[16..24].copy_from_slice(&rep.0[3].to_be_bytes());
	result[24..32].copy_from_slice(&rep.0[2].to_be_bytes());
	result[32..40].copy_from_slice(&rep.0[1].to_be_bytes());
	result[40..48].copy_from_slice(&rep.0[0].to_be_bytes());

	result
}

pub(crate) fn read_fq_with_offset(
	bytes: &[u8],
	offset: usize,
	mask: bool,
) -> Result<Fq, ark_serialize::SerializationError> {
	let mut tmp = [0; G1_SERIALIZED_SIZE];
	// read `G1_SERIALIZED_SIZE` bytes
	tmp.copy_from_slice(&bytes[offset * G1_SERIALIZED_SIZE..G1_SERIALIZED_SIZE * (offset + 1)]);

	if mask {
		// Mask away the flag bits
		tmp[0] &= 0b0001_1111;
	}
	deserialize_fq(tmp).ok_or(SerializationError::InvalidData)
}

pub(crate) fn read_g1_compressed<R: ark_serialize::Read>(
	mut reader: R,
) -> Result<Affine<G1Config>, ark_serialize::SerializationError> {
	let mut bytes = [0u8; G1_SERIALIZED_SIZE];
	reader.read_exact(&mut bytes).ok().ok_or(SerializationError::InvalidData)?;

	// Obtain the three flags from the start of the byte sequence
	let flags = EncodingFlags::get_flags(&bytes[..]);

	// we expect to be deserializing a compressed point
	if !flags.is_compressed {
		return Err(SerializationError::UnexpectedFlags)
	}

	if flags.is_infinity {
		return Ok(G1Affine::zero())
	}

	// Attempt to obtain the x-coordinate
	let x = read_fq_with_offset(&bytes, 0, true)?;

	let p = G1Affine::get_point_from_x_unchecked(x, flags.is_lexographically_largest)
		.ok_or(SerializationError::InvalidData)?;

	Ok(p)
}

pub(crate) fn read_g1_uncompressed<R: ark_serialize::Read>(
	mut reader: R,
) -> Result<Affine<G1Config>, ark_serialize::SerializationError> {
	let mut bytes = [0u8; 2 * G1_SERIALIZED_SIZE];
	reader.read_exact(&mut bytes).map_err(|_| SerializationError::InvalidData)?;

	// Obtain the three flags from the start of the byte sequence
	let flags = EncodingFlags::get_flags(&bytes[..]);

	// we expect to be deserializing an uncompressed point
	if flags.is_compressed {
		return Err(SerializationError::UnexpectedFlags)
	}

	if flags.is_infinity {
		return Ok(G1Affine::zero())
	}

	// Attempt to obtain the x-coordinate
	let x = read_fq_with_offset(&bytes, 0, true)?;
	// Attempt to obtain the y-coordinate
	let y = read_fq_with_offset(&bytes, 1, false)?;

	let p = G1Affine::new_unchecked(x, y);

	Ok(p)
}

pub(crate) fn read_g2_compressed<R: ark_serialize::Read>(
	mut reader: R,
) -> Result<Affine<G2Config>, ark_serialize::SerializationError> {
	let mut bytes = [0u8; G2_SERIALIZED_SIZE];
	reader.read_exact(&mut bytes).map_err(|_| SerializationError::InvalidData)?;

	// Obtain the three flags from the start of the byte sequence
	let flags = EncodingFlags::get_flags(&bytes);

	// we expect to be deserializing a compressed point
	if !flags.is_compressed {
		return Err(SerializationError::UnexpectedFlags)
	}

	if flags.is_infinity {
		return Ok(G2Affine::zero())
	}

	// Attempt to obtain the x-coordinate
	let xc1 = read_fq_with_offset(&bytes, 0, true)?;
	let xc0 = read_fq_with_offset(&bytes, 1, false)?;

	let x = Fq2::new(xc0, xc1);

	let p = G2Affine::get_point_from_x_unchecked(x, flags.is_lexographically_largest)
		.ok_or(SerializationError::InvalidData)?;

	Ok(p)
}

pub(crate) fn read_g2_uncompressed<R: ark_serialize::Read>(
	mut reader: R,
) -> Result<Affine<G2Config>, ark_serialize::SerializationError> {
	let mut bytes = [0u8; 2 * G2_SERIALIZED_SIZE];
	reader.read_exact(&mut bytes).map_err(|_| SerializationError::InvalidData)?;

	// Obtain the three flags from the start of the byte sequence
	let flags = EncodingFlags::get_flags(&bytes);

	// we expect to be deserializing an uncompressed point
	if flags.is_compressed {
		return Err(SerializationError::UnexpectedFlags)
	}

	if flags.is_infinity {
		return Ok(G2Affine::zero())
	}

	// Attempt to obtain the x-coordinate
	let xc1 = read_fq_with_offset(&bytes, 0, true)?;
	let xc0 = read_fq_with_offset(&bytes, 1, false)?;
	let x = Fq2::new(xc0, xc1);

	// Attempt to obtain the y-coordinate
	let yc1 = read_fq_with_offset(&bytes, 2, false)?;
	let yc0 = read_fq_with_offset(&bytes, 3, false)?;
	let y = Fq2::new(yc0, yc1);

	let p = G2Affine::new_unchecked(x, y);

	Ok(p)
}
