use blake2_rfc;
use twox_hash;

/// Do a Blake2 512-bit hash and place result in `dest`.
pub fn blake2_512_into(data: &[u8], dest: &mut[u8; 64]) {
	dest.copy_from_slice(blake2_rfc::blake2b::blake2b(64, &[], data).as_bytes());
}

/// Do a Blake2 512-bit hash and return result.
pub fn blake2_512(data: &[u8]) -> [u8; 64] {
	let mut r: [u8; 64] = unsafe { ::std::mem::uninitialized() };
	blake2_512_into(data, &mut r);
	r
}

/// Do a Blake2 256-bit hash and place result in `dest`.
pub fn blake2_256_into(data: &[u8], dest: &mut[u8; 32]) {
	dest.copy_from_slice(blake2_rfc::blake2b::blake2b(32, &[], data).as_bytes());
}

/// Do a Blake2 256-bit hash and return result.
pub fn blake2_256(data: &[u8]) -> [u8; 32] {
	let mut r: [u8; 32] = unsafe { ::std::mem::uninitialized() };
	blake2_256_into(data, &mut r);
	r
}

/// Do a Blake2 128-bit hash and place result in `dest`.
pub fn blake2_128_into(data: &[u8], dest: &mut[u8; 16]) {
	dest.copy_from_slice(blake2_rfc::blake2b::blake2b(16, &[], data).as_bytes());
}

/// Do a Blake2 128-bit hash and return result.
pub fn blake2_128(data: &[u8]) -> [u8; 16] {
	let mut r: [u8; 16] = unsafe { ::std::mem::uninitialized() };
	blake2_128_into(data, &mut r);
	r
}

/// Do a XX 128-bit hash and place result in `dest`.
pub fn twox_128_into(data: &[u8], dest: &mut [u8; 16]) {
	use ::std::hash::Hasher;
	let mut h0 = twox_hash::XxHash::with_seed(0);
	let mut h1 = twox_hash::XxHash::with_seed(1);
	h0.write(data);
	h1.write(data);
	let r0 = h0.finish();
	let r1 = h1.finish();
	use byteorder::{ByteOrder, LittleEndian};
	LittleEndian::write_u64(&mut dest[0..8], r0);
	LittleEndian::write_u64(&mut dest[8..16], r1);
}

/// Do a XX 128-bit hash and return result.
pub fn twox_128(data: &[u8]) -> [u8; 16] {
	let mut r: [u8; 16] = unsafe { ::std::mem::uninitialized() };
	twox_128_into(data, &mut r);
	r
}

/// Do a XX 256-bit hash and place result in `dest`.
pub fn twox_256_into(data: &[u8], dest: &mut [u8; 32]) {
	use ::std::hash::Hasher;
	use byteorder::{ByteOrder, LittleEndian};
	let mut h0 = twox_hash::XxHash::with_seed(0);
	let mut h1 = twox_hash::XxHash::with_seed(1);
	let mut h2 = twox_hash::XxHash::with_seed(2);
	let mut h3 = twox_hash::XxHash::with_seed(3);
	h0.write(data);
	h1.write(data);
	h2.write(data);
	h3.write(data);
	let r0 = h0.finish();
	let r1 = h1.finish();
	let r2 = h2.finish();
	let r3 = h3.finish();
	LittleEndian::write_u64(&mut dest[0..8], r0);
	LittleEndian::write_u64(&mut dest[8..16], r1);
	LittleEndian::write_u64(&mut dest[16..24], r2);
	LittleEndian::write_u64(&mut dest[24..32], r3);
}

/// Do a XX 256-bit hash and return result.
pub fn twox_256(data: &[u8]) -> [u8; 32] {
	let mut r: [u8; 32] = unsafe { ::std::mem::uninitialized() };
	twox_256_into(data, &mut r);
	r
}
