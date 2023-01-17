use ark_serialize::{CanonicalSerialize, Compress};
use ark_std::{io::Cursor, vec};

pub fn serialize_result(result: impl CanonicalSerialize) -> Vec<u8> {
	let mut serialized_result = vec![0u8; result.serialized_size(Compress::Yes)];
	let mut cursor = Cursor::new(&mut serialized_result[..]);
	result.serialize_compressed(&mut cursor).unwrap();
	serialized_result
}
