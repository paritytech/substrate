use primitives::Timestamp;
use storable::Storable;

pub fn get() -> Timestamp {
	Storable::lookup_default(b"tim:val")
}

pub fn set(now: Timestamp) {
	now.store(b"tim:val")
}

#[cfg(test)]
mod tests {
	use joiner::Joiner;
	use keyedvec::KeyedVec;
	use runtime_support::{with_externalities, twox_128};
	use runtime::timestamp;
	use testing::TestExternalities;

	#[test]
	fn timestamp_works() {
		let mut t = TestExternalities { storage: map![
			twox_128(b"tim:val").to_vec() => vec![].join(&42u64)
		], };

		with_externalities(&mut t, || {
			assert_eq!(timestamp::get(), 42);
			timestamp::set(69);
			assert_eq!(timestamp::get(), 69);
		});
	}
}
