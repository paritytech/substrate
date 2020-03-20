// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Shareable Substrate traits.

use crate::{crypto::KeyTypeId, ed25519, sr25519};

use std::{
	fmt::{Debug, Display},
	panic::UnwindSafe,
	sync::Arc,
};

pub use sp_externalities::{Externalities, ExternalitiesExt};

/// Something that generates, stores and provides access to keys.
pub trait BareCryptoStore: Send + Sync {
	/// Returns all sr25519 public keys for the given key type.
	fn sr25519_public_keys(&self, id: KeyTypeId) -> Vec<sr25519::Public>;
	/// Generate a new sr25519 key pair for the given key type and an optional seed.
	///
	/// If the given seed is `Some(_)`, the key pair will only be stored in memory.
	///
	/// Returns the public key of the generated key pair.
	fn sr25519_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<sr25519::Public, String>;
	/// Returns the sr25519 key pair for the given key type and public key combination.
	fn sr25519_key_pair(&self, id: KeyTypeId, pub_key: &sr25519::Public) -> Option<sr25519::Pair>;

	/// Returns all ed25519 public keys for the given key type.
	fn ed25519_public_keys(&self, id: KeyTypeId) -> Vec<ed25519::Public>;
	/// Generate a new ed25519 key pair for the given key type and an optional seed.
	///
	/// If the given seed is `Some(_)`, the key pair will only be stored in memory.
	///
	/// Returns the public key of the generated key pair.
	fn ed25519_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<ed25519::Public, String>;

	/// Returns the ed25519 key pair for the given key type and public key combination.
	fn ed25519_key_pair(&self, id: KeyTypeId, pub_key: &ed25519::Public) -> Option<ed25519::Pair>;

	/// Insert a new key. This doesn't require any known of the crypto; but a public key must be
	/// manually provided.
	///
	/// Places it into the file system store.
	///
	/// `Err` if there's some sort of weird filesystem error, but should generally be `Ok`.
	fn insert_unknown(&mut self, _key_type: KeyTypeId, _suri: &str, _public: &[u8]) -> Result<(), ()>;

	/// Get the password for this store.
	fn password(&self) -> Option<&str>;

	/// Checks if the private keys for the given public key and key type combinations exist.
	///
	/// Returns `true` iff all private keys could be found.
	fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool;
}

/// A pointer to the key store.
pub type BareCryptoStorePtr = Arc<parking_lot::RwLock<dyn BareCryptoStore>>;

sp_externalities::decl_extension! {
	/// The keystore extension to register/retrieve from the externalities.
	pub struct KeystoreExt(BareCryptoStorePtr);
}

/// Code execution engine.
pub trait CodeExecutor: Sized + Send + Sync + CallInWasm + Clone + 'static {
	/// Externalities error type.
	type Error: Display + Debug + Send + 'static;

	/// Call a given method in the runtime. Returns a tuple of the result (either the output data
	/// or an execution error) together with a `bool`, which is true if native execution was used.
	fn call<
		E: Externalities,
		R: codec::Codec + PartialEq,
		NC: FnOnce() -> Result<R, String> + UnwindSafe,
	>(
		&self,
		ext: &mut E,
		runtime_code: &RuntimeCode,
		method: &str,
		data: &[u8],
		use_native: bool,
		native_call: Option<NC>,
	) -> (Result<crate::NativeOrEncoded<R>, Self::Error>, bool);
}


/// The Wasm code of a Substrate runtime.
#[derive(Debug, Clone, codec::Encode, codec::Decode)]
pub struct RuntimeCode {
	/// The actual Wasm code as binary blob.
	pub code: Vec<u8>,
	/// The optional heap pages this `code` should be executed with.
	///
	/// If `None` are given, the default value of the executor will be used.
	pub heap_pages: Option<u64>,
	/// The SCALE encoded hash of `code`.
	///
	/// The hashing algorithm isn't that important, as long as all runtime
	/// code instances use the same.
	pub hash: Vec<u8>,
}

impl PartialEq for RuntimeCode {
	fn eq(&self, other: &Self) -> bool {
		self.hash == other.hash
	}
}

impl RuntimeCode {
	/// Create an `RuntimeCode` instance from the given `Externalities`.
	///
	/// Extracts the code and the heap pages using the well known keys.
	///
	/// Returns an error if the code could not be found.
	pub fn from_externalities(ext: &dyn Externalities) -> Result<Self, CodeNotFound> {
		let code = ext.storage(sp_storage::well_known_keys::CODE).ok_or(CodeNotFound)?;
		let hash = ext.storage_hash(sp_storage::well_known_keys::CODE).ok_or(CodeNotFound)?;
		let heap_pages = ext.storage(sp_storage::well_known_keys::HEAP_PAGES)
			.and_then(|hp| codec::Decode::decode(&mut &hp[..]).ok());

		Ok(Self {
			code,
			hash,
			heap_pages,
		})
	}

	/// Create an empty instance.
	///
	/// This is only useful for tests that don't want to execute any code.
	pub fn empty() -> Self {
		Self {
			code: Vec::new(),
			hash: Vec::new(),
			heap_pages: None,
		}
	}
}

/// Could not find the `:code` in the externalities while initializing the [`RuntimeCode`].
#[derive(Debug)]
pub struct CodeNotFound;

impl std::fmt::Display for CodeNotFound {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
		write!(f, "the storage entry `:code` doesn't have any code")
	}
}

/// Something that can call a method in a WASM blob.
pub trait CallInWasm: Send + Sync {
	/// Call the given `method` in the given `wasm_blob` using `call_data` (SCALE encoded arguments)
	/// to decode the arguments for the method.
	///
	/// Returns the SCALE encoded return value of the method.
	fn call_in_wasm(
		&self,
		wasm_blob: &[u8],
		method: &str,
		call_data: &[u8],
		ext: &mut dyn Externalities,
	) -> Result<Vec<u8>, String>;
}

sp_externalities::decl_extension! {
	/// The call-in-wasm extension to register/retrieve from the externalities.
	pub struct CallInWasmExt(Box<dyn CallInWasm>);
}

impl CallInWasmExt {
	/// Creates a new instance of `Self`.
	pub fn new<T: CallInWasm + 'static>(inner: T) -> Self {
		Self(Box::new(inner))
	}
}
