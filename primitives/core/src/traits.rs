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

use crate::{
	crypto::{KeyTypeId, CryptoTypePublicPair},
	ed25519, sr25519,
};

use std::{
	borrow::Cow,
	fmt::{Debug, Display},
	panic::UnwindSafe,
	sync::Arc,
};

pub use sp_externalities::{Externalities, ExternalitiesExt};

/// BareCryptoStore error
#[derive(Debug)]
pub enum BareCryptoStoreError {
	/// Public key type is not supported
	KeyNotSupported(KeyTypeId),
	/// Pair not found for public key and KeyTypeId
	PairNotFound(String),
	/// Validation error
	ValidationError(String),
	/// Keystore unavailable
	Unavailable,
	/// Programming errors
	Other(String)
}

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
	) -> Result<sr25519::Public, BareCryptoStoreError>;
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
	) -> Result<ed25519::Public, BareCryptoStoreError>;

	/// Insert a new key. This doesn't require any known of the crypto; but a public key must be
	/// manually provided.
	///
	/// Places it into the file system store.
	///
	/// `Err` if there's some sort of weird filesystem error, but should generally be `Ok`.
	fn insert_unknown(&mut self, _key_type: KeyTypeId, _suri: &str, _public: &[u8]) -> Result<(), ()>;

	/// Get the password for this store.
	fn password(&self) -> Option<&str>;
	/// Find intersection between provided keys and supported keys
	///
	/// Provided a list of (CryptoTypeId,[u8]) pairs, this would return
	/// a filtered set of public keys which are supported by the keystore.
	fn supported_keys(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>
	) -> Result<Vec<CryptoTypePublicPair>, BareCryptoStoreError>;
	/// List all supported keys
	///
	/// Returns a set of public keys the signer supports.
	fn keys(&self, id: KeyTypeId) -> Result<Vec<CryptoTypePublicPair>, BareCryptoStoreError>;

	/// Checks if the private keys for the given public key and key type combinations exist.
	///
	/// Returns `true` iff all private keys could be found.
	fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool;

	/// Sign with key
	///
	/// Signs a message with the private key that matches
	/// the public key passed.
	///
	/// Returns the SCALE encoded signature if key is found & supported,
	/// an error otherwise.
	fn sign_with(
		&self,
		id: KeyTypeId,
		key: &CryptoTypePublicPair,
		msg: &[u8],
	) -> Result<Vec<u8>, BareCryptoStoreError>;

	/// Sign with any key
	///
	/// Given a list of public keys, find the first supported key and
	/// sign the provided message with that key.
	///
	/// Returns a tuple of the used key and the SCALE encoded signature.
	fn sign_with_any(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>,
		msg: &[u8]
	) -> Result<(CryptoTypePublicPair, Vec<u8>), BareCryptoStoreError> {
		if keys.len() == 1 {
			return self.sign_with(id, &keys[0], msg).map(|s| (keys[0].clone(), s));
		} else {
			for k in self.supported_keys(id, keys)? {
				if let Ok(sign) = self.sign_with(id, &k, msg) {
					return Ok((k, sign));
				}
			}
		}
		Err(BareCryptoStoreError::KeyNotSupported(id))
	}

	/// Sign with all keys
	///
	/// Provided a list of public keys, sign a message with
	/// each key given that the key is supported.
	///
	/// Returns a list of `Result`s each representing the SCALE encoded
	/// signature of each key or a BareCryptoStoreError for non-supported keys.
	fn sign_with_all(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>,
		msg: &[u8],
	) -> Result<Vec<Result<Vec<u8>, BareCryptoStoreError>>, ()>{
		Ok(keys.iter().map(|k| self.sign_with(id, k, msg)).collect())
	}
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
		R: codec::Codec + PartialEq,
		NC: FnOnce() -> Result<R, String> + UnwindSafe,
	>(
		&self,
		ext: &mut dyn Externalities,
		runtime_code: &RuntimeCode,
		method: &str,
		data: &[u8],
		use_native: bool,
		native_call: Option<NC>,
	) -> (Result<crate::NativeOrEncoded<R>, Self::Error>, bool);
}

/// Something that can fetch the runtime `:code`.
pub trait FetchRuntimeCode {
	/// Fetch the runtime `:code`.
	///
	/// If the `:code` could not be found/not available, `None` should be returned.
	fn fetch_runtime_code<'a>(&'a self) -> Option<Cow<'a, [u8]>>;
}

/// Wrapper to use a `u8` slice or `Vec` as [`FetchRuntimeCode`].
pub struct WrappedRuntimeCode<'a>(pub std::borrow::Cow<'a, [u8]>);

impl<'a> FetchRuntimeCode for WrappedRuntimeCode<'a> {
	fn fetch_runtime_code<'b>(&'b self) -> Option<Cow<'b, [u8]>> {
		Some(self.0.as_ref().into())
	}
}

/// Type that implements [`FetchRuntimeCode`] and always returns `None`.
pub struct NoneFetchRuntimeCode;

impl FetchRuntimeCode for NoneFetchRuntimeCode {
	fn fetch_runtime_code<'a>(&'a self) -> Option<Cow<'a, [u8]>> {
		None
	}
}

/// The Wasm code of a Substrate runtime.
#[derive(Clone)]
pub struct RuntimeCode<'a> {
	/// The code fetcher that can be used to lazily fetch the code.
	pub code_fetcher: &'a dyn FetchRuntimeCode,
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

impl<'a> PartialEq for RuntimeCode<'a> {
	fn eq(&self, other: &Self) -> bool {
		self.hash == other.hash
	}
}

impl<'a> RuntimeCode<'a> {
	/// Create an empty instance.
	///
	/// This is only useful for tests that don't want to execute any code.
	pub fn empty() -> Self {
		Self {
			code_fetcher: &NoneFetchRuntimeCode,
			hash: Vec::new(),
			heap_pages: None,
		}
	}
}

impl<'a> FetchRuntimeCode for RuntimeCode<'a> {
	fn fetch_runtime_code<'b>(&'b self) -> Option<Cow<'b, [u8]>> {
		self.code_fetcher.fetch_runtime_code()
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

/// `Allow` or `Disallow` missing host functions when instantiating a WASM blob.
#[derive(Clone, Copy, Debug)]
pub enum MissingHostFunctions {
	/// Any missing host function will be replaced by a stub that returns an error when
	/// being called.
	Allow,
	/// Any missing host function will result in an error while instantiating the WASM blob,
	Disallow,
}

impl MissingHostFunctions {
	/// Are missing host functions allowed?
	pub fn allowed(self) -> bool {
		matches!(self, Self::Allow)
	}
}

/// Something that can call a method in a WASM blob.
pub trait CallInWasm: Send + Sync {
	/// Call the given `method` in the given `wasm_blob` using `call_data` (SCALE encoded arguments)
	/// to decode the arguments for the method.
	///
	/// Returns the SCALE encoded return value of the method.
	///
	/// # Note
	///
	/// If `code_hash` is `Some(_)` the `wasm_code` module and instance will be cached internally,
	/// otherwise it is thrown away after the call.
	fn call_in_wasm(
		&self,
		wasm_code: &[u8],
		code_hash: Option<Vec<u8>>,
		method: &str,
		call_data: &[u8],
		ext: &mut dyn Externalities,
		missing_host_functions: MissingHostFunctions,
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

/// Something that can spawn tasks and also can be cloned.
pub trait CloneableSpawn: futures::task::Spawn + Send + Sync {
	/// Clone as heap-allocated handle.
	fn clone(&self) -> Box<dyn CloneableSpawn>;
}

sp_externalities::decl_extension! {
	/// Task executor extension.
	pub struct TaskExecutorExt(Box<dyn CloneableSpawn>);
}

impl TaskExecutorExt {
	/// New instance of task executor extension.
	pub fn new(spawn_handle: Box<dyn CloneableSpawn>) -> Self {
		Self(spawn_handle)
	}
}

/// Something that can spawn a blocking future.
pub trait SpawnBlocking {
	/// Spawn the given blocking future.
	///
	/// The given `name` is used to identify the future in tracing.
	fn spawn_blocking(&self, name: &'static str, future: futures::future::BoxFuture<'static, ()>);
}
