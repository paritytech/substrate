use runtime_support::Vec;
use keyedvec::KeyedVec;
use storage::Storage;

/// A trait to conveniently store a vector of storable data.
// TODO: add iterator support
pub trait StorageVec {
	type Item: Default + Sized + Storage;
	const PREFIX: &'static [u8];

	/// Get the current set of items.
	fn items() -> Vec<Self::Item> {
		(0..Self::count()).into_iter().map(Self::item).collect()
	}

	/// Set the current set of items.
	fn set_items(items: &[Self::Item]) {
		Self::set_count(items.len() as u32);
		items.iter().enumerate().for_each(|(v, ref i)| Self::set_item(v as u32, i));
	}

	fn set_item(index: u32, item: &Self::Item) {
		item.store(&index.to_keyed_vec(Self::PREFIX));
	}

	fn item(index: u32) -> Self::Item {
		Storage::into(&index.to_keyed_vec(Self::PREFIX))
	}

	fn set_count(count: u32) {
		(count..Self::count()).for_each(|i| Self::set_item(i, &Self::Item::default()));
		count.store(&b"len".to_keyed_vec(Self::PREFIX));
	}

	fn count() -> u32 {
		Storage::into(&b"len".to_keyed_vec(Self::PREFIX))
	}
}
