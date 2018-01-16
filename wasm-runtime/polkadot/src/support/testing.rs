use runtime_support::{NoError, Externalities};
use std::collections::HashMap;

#[derive(Debug, Default)]
pub struct TestExternalities {
	pub storage: HashMap<Vec<u8>, Vec<u8>>,
}

impl Externalities for TestExternalities {
	type Error = NoError;

	fn storage(&self, key: &[u8]) -> Result<&[u8], NoError> {
		Ok(self.storage.get(&key.to_vec()).map_or(&[] as &[u8], Vec::as_slice))
	}

	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
		self.storage.insert(key, value);
	}
}
