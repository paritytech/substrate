use slicable::Slicable;
use endiansensitive::EndianSensitive;
use runtime_support;

pub trait Storage {
	fn into(key: &[u8]) -> Self where Self: Sized + Default { Self::try_into(key).unwrap_or_else(Default::default) }
	fn try_into(_key: &[u8]) -> Option<Self> where Self: Sized { unimplemented!() }
	fn store(&self, key: &[u8]);
}

impl<T: Default + Sized + EndianSensitive> Storage for T {
	fn try_into(key: &[u8]) -> Option<Self> {
		Slicable::set_as_slice(|out| runtime_support::read_storage(key, out) == out.len())
	}
	fn store(&self, key: &[u8]) {
		self.as_slice_then(|slice| runtime_support::set_storage(key, slice));
	}
}

impl Storage for [u8] {
	fn store(&self, key: &[u8]) {
		runtime_support::set_storage(key, self)
	}
}
