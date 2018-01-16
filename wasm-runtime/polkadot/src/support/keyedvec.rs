use primitives::AccountID;
use slicable::Slicable;

pub trait KeyedVec {
	fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8>;
}

impl KeyedVec for AccountID {
	fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8> {
		let mut r = prepend_key.to_vec();
		r.extend_from_slice(self);
		r
	}
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

impl_endians!(u16, u32, u64, usize, i16, i32, i64, isize);
