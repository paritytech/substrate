use slicable::Slicable;
use endiansensitive::EndianSensitive;
use runtime_support;

pub trait Storage {
	fn into(key: &[u8]) -> Self;
	fn store(&self, key: &[u8]);
}

impl<T: Default + Sized + EndianSensitive> Storage for T {
	fn into(key: &[u8]) -> Self {
		Slicable::set_as_slice(|out| runtime_support::read_storage(key, out) == out.len())
			.unwrap_or_else(Default::default)
	}

	fn store(&self, key: &[u8]) {
		self.as_slice_then(|slice| runtime_support::set_storage(key, slice));
	}
}

pub fn storage_into<T: Storage>(key: &[u8]) -> T {
	T::into(key)
}
