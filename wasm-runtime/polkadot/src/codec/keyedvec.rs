use runtime_support::Vec;
use slicable::Slicable;

pub trait KeyedVec {
	fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8>;
}

macro_rules! impl_non_endians {
	( $( $t:ty ),* ) => { $(
		impl KeyedVec for $t {
			fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8> {
				let mut r = prepend_key.to_vec();
				r.extend_from_slice(&self[..]);
				r
			}
		}
	)* }
}

macro_rules! impl_endians {
	( $( $t:ty ),* ) => { $(
		impl KeyedVec for $t {
			fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8> {
				self.as_slice_then(|slice| {
					let mut r = prepend_key.to_vec();
					r.extend_from_slice(slice);
					r
				})
			}
		}
	)* }
}

impl_endians!(u8, i8, u16, u32, u64, usize, i16, i32, i64, isize);
impl_non_endians!([u8; 1], [u8; 2], [u8; 3], [u8; 4], [u8; 5], [u8; 6], [u8; 7], [u8; 8],
	[u8; 10], [u8; 12], [u8; 14], [u8; 16], [u8; 20], [u8; 24], [u8; 28], [u8; 32], [u8; 40],
	[u8; 48], [u8; 56], [u8; 64], [u8; 80], [u8; 96], [u8; 112], [u8; 128]);
