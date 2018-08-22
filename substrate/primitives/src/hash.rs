// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! A fixed hash type.

#[cfg(feature = "std")]
use serde::{Serialize, Serializer, Deserialize, Deserializer};

#[cfg(feature = "std")]
use bytes;
#[cfg(feature = "std")]
use core::cmp;
#[cfg(feature = "std")]
use rlp::{Rlp, RlpStream, DecoderError};

macro_rules! impl_rest {
	($name: ident, $len: expr) => {
		#[cfg(feature = "std")]
		impl Serialize for $name {
			fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
				bytes::serialize(&self.0, serializer)
			}
		}

		#[cfg(feature = "std")]
		impl<'de> Deserialize<'de> for $name {
			fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'de> {
				bytes::deserialize_check_len(deserializer, bytes::ExpectedLen::Exact($len))
					.map(|x| (&*x).into())
			}
		}

		impl ::codec::Encode for $name {
			fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
				self.0.using_encoded(f)
			}
		}
		impl ::codec::Decode for $name {
			fn decode<I: ::codec::Input>(input: &mut I) -> Option<Self> {
				<[u8; $len] as ::codec::Decode>::decode(input).map($name)
			}
		}

		#[cfg(feature = "std")]
		impl ::rlp::Encodable for $name {
			fn rlp_append(&self, s: &mut RlpStream) {
				s.encoder().encode_value(self);
			}
		}

		#[cfg(feature = "std")]
		impl ::rlp::Decodable for $name {
			fn decode(rlp: &Rlp) -> Result<Self, DecoderError> {
				rlp.decoder().decode_value(|bytes| match bytes.len().cmp(&$len) {
					cmp::Ordering::Less => Err(DecoderError::RlpIsTooShort),
					cmp::Ordering::Greater => Err(DecoderError::RlpIsTooBig),
					cmp::Ordering::Equal => {
						let mut t = [0u8; $len];
						t.copy_from_slice(bytes);
						Ok($name(t))
					}
				})
			}
		}

	}
}

construct_hash!(H160, 20);
construct_hash!(H256, 32);
construct_hash!(H512, 64);
impl_rest!(H160, 20);
impl_rest!(H256, 32);
impl_rest!(H512, 64);

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_serializer as ser;
	use rlp::{Encodable, RlpStream};

	#[test]
	fn test_hash_is_encodable() {
		let h = H160::from(21);
		let mut s = RlpStream::new();
		h.rlp_append(&mut s);
		assert_eq!(s.drain().into_vec(), &[148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21]);
	}

	#[test]
	fn test_hash_is_decodable() {
		let data = vec![148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 123];
		let res = ::rlp::decode::<H160>(&data);
		assert!(res.is_ok());
		assert_eq!(res.unwrap(), H160::from(123));

		let res = ::rlp::decode::<H256>(&data);
		assert!(res.is_err());
	}

	#[test]
	fn test_h160() {
		let tests = vec![
			(Default::default(), "0x0000000000000000000000000000000000000000"),
			(H160::from(2), "0x0000000000000000000000000000000000000002"),
			(H160::from(15), "0x000000000000000000000000000000000000000f"),
			(H160::from(16), "0x0000000000000000000000000000000000000010"),
			(H160::from(1_000), "0x00000000000000000000000000000000000003e8"),
			(H160::from(100_000), "0x00000000000000000000000000000000000186a0"),
			(H160::from(u64::max_value()), "0x000000000000000000000000ffffffffffffffff"),
		];

		for (number, expected) in tests {
			assert_eq!(format!("{:?}", expected), ser::to_string_pretty(&number));
			assert_eq!(number, ser::from_str(&format!("{:?}", expected)).unwrap());
		}
	}

	#[test]
	fn test_h256() {
		let tests = vec![
			(Default::default(), "0x0000000000000000000000000000000000000000000000000000000000000000"),
			(H256::from(2), "0x0000000000000000000000000000000000000000000000000000000000000002"),
			(H256::from(15), "0x000000000000000000000000000000000000000000000000000000000000000f"),
			(H256::from(16), "0x0000000000000000000000000000000000000000000000000000000000000010"),
			(H256::from(1_000), "0x00000000000000000000000000000000000000000000000000000000000003e8"),
			(H256::from(100_000), "0x00000000000000000000000000000000000000000000000000000000000186a0"),
			(H256::from(u64::max_value()), "0x000000000000000000000000000000000000000000000000ffffffffffffffff"),
		];

		for (number, expected) in tests {
			assert_eq!(format!("{:?}", expected), ser::to_string_pretty(&number));
			assert_eq!(number, ser::from_str(&format!("{:?}", expected)).unwrap());
		}
	}

	#[test]
	fn test_invalid() {
		assert!(ser::from_str::<H256>("\"0x000000000000000000000000000000000000000000000000000000000000000\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"0x000000000000000000000000000000000000000000000000000000000000000g\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"0x00000000000000000000000000000000000000000000000000000000000000000\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"0\"").unwrap_err().is_data());
		assert!(ser::from_str::<H256>("\"10\"").unwrap_err().is_data());
	}

	#[test]
	fn test_heapsizeof() {
		use heapsize::HeapSizeOf;
		let h = H256::new();
		assert_eq!(h.heap_size_of_children(), 0);
	}
}
