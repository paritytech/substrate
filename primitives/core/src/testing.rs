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

//! Types that should only be used for testing!

use crate::crypto::KeyTypeId;
#[cfg(feature = "std")]
use crate::{
	crypto::{Pair, Public, CryptoTypePublicPair},
	ed25519, sr25519,
	traits::BareCryptoStoreError
};
#[cfg(feature = "std")]
use std::collections::HashSet;
/// Key type for generic Ed25519 key.
pub const ED25519: KeyTypeId = KeyTypeId(*b"ed25");
/// Key type for generic Sr 25519 key.
pub const SR25519: KeyTypeId = KeyTypeId(*b"sr25");

/// A keystore implementation usable in tests.
#[cfg(feature = "std")]
#[derive(Default)]
pub struct KeyStore {
	/// `KeyTypeId` maps to public keys and public keys map to private keys.
	keys: std::collections::HashMap<KeyTypeId, std::collections::HashMap<Vec<u8>, String>>,
}

#[cfg(feature = "std")]
impl KeyStore {
	/// Creates a new instance of `Self`.
	pub fn new() -> crate::traits::BareCryptoStorePtr {
		std::sync::Arc::new(parking_lot::RwLock::new(Self::default()))
	}

	fn sr25519_key_pair(&self, id: KeyTypeId, pub_key: &sr25519::Public) -> Option<sr25519::Pair> {
		self.keys.get(&id)
			.and_then(|inner|
				inner.get(pub_key.as_slice())
					.map(|s| sr25519::Pair::from_string(s, None).expect("`sr25519` seed slice is valid"))
			)
	}

	fn ed25519_key_pair(&self, id: KeyTypeId, pub_key: &ed25519::Public) -> Option<ed25519::Pair> {
		self.keys.get(&id)
			.and_then(|inner|
				inner.get(pub_key.as_slice())
					.map(|s| ed25519::Pair::from_string(s, None).expect("`ed25519` seed slice is valid"))
			)
	}

}

#[cfg(feature = "std")]
impl crate::traits::BareCryptoStore for KeyStore {
	fn keys(&self, id: KeyTypeId) -> Result<Vec<CryptoTypePublicPair>, BareCryptoStoreError> {
		self.keys
			.get(&id)
			.map(|map| {
				Ok(map.keys()
					.fold(Vec::new(), |mut v, k| {
						v.push(CryptoTypePublicPair(sr25519::CRYPTO_ID, k.clone()));
						v.push(CryptoTypePublicPair(ed25519::CRYPTO_ID, k.clone()));
						v
					}))
			})
			.unwrap_or(Ok(vec![]))
	}

	fn sr25519_public_keys(&self, id: KeyTypeId) -> Vec<sr25519::Public> {
		self.keys.get(&id)
			.map(|keys|
				keys.values()
					.map(|s| sr25519::Pair::from_string(s, None).expect("`sr25519` seed slice is valid"))
					.map(|p| p.public())
					.collect()
			)
			.unwrap_or_default()
	}

	fn sr25519_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<sr25519::Public, BareCryptoStoreError> {
		match seed {
			Some(seed) => {
				let pair = sr25519::Pair::from_string(seed, None)
					.map_err(|_| BareCryptoStoreError::ValidationError("Generates an `sr25519` pair.".to_owned()))?;
				self.keys.entry(id).or_default().insert(pair.public().to_raw_vec(), seed.into());
				Ok(pair.public())
			},
			None => {
				let (pair, phrase, _) = sr25519::Pair::generate_with_phrase(None);
				self.keys.entry(id).or_default().insert(pair.public().to_raw_vec(), phrase);
				Ok(pair.public())
			}
		}
	}

	fn ed25519_public_keys(&self, id: KeyTypeId) -> Vec<ed25519::Public> {
		self.keys.get(&id)
			.map(|keys|
				keys.values()
					.map(|s| ed25519::Pair::from_string(s, None).expect("`ed25519` seed slice is valid"))
					.map(|p| p.public())
					.collect()
			)
			.unwrap_or_default()
	}

	fn ed25519_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<ed25519::Public, BareCryptoStoreError> {
		match seed {
			Some(seed) => {
				let pair = ed25519::Pair::from_string(seed, None)
					.map_err(|_| BareCryptoStoreError::ValidationError("Generates an `ed25519` pair.".to_owned()))?;
				self.keys.entry(id).or_default().insert(pair.public().to_raw_vec(), seed.into());
				Ok(pair.public())
			},
			None => {
				let (pair, phrase, _) = ed25519::Pair::generate_with_phrase(None);
				self.keys.entry(id).or_default().insert(pair.public().to_raw_vec(), phrase);
				Ok(pair.public())
			}
		}
	}

	fn insert_unknown(&mut self, id: KeyTypeId, suri: &str, public: &[u8]) -> Result<(), ()> {
		self.keys.entry(id).or_default().insert(public.to_owned(), suri.to_string());
		Ok(())
	}

	fn password(&self) -> Option<&str> {
		None
	}

	fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool {
		public_keys.iter().all(|(k, t)| self.keys.get(&t).and_then(|s| s.get(k)).is_some())
	}

	fn supported_keys(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>,
	) -> std::result::Result<Vec<CryptoTypePublicPair>, BareCryptoStoreError> {
		let provided_keys = keys.into_iter().collect::<HashSet<_>>();
		let all_keys = self.keys(id)?.into_iter().collect::<HashSet<_>>();

		Ok(provided_keys.intersection(&all_keys).cloned().collect())
	}

	fn sign_with(
		&self,
		id: KeyTypeId,
		key: &CryptoTypePublicPair,
		msg: &[u8],
	) -> Result<Vec<u8>, BareCryptoStoreError> {
		use codec::Encode;

		match key.0 {
			ed25519::CRYPTO_ID => {
				let key_pair: ed25519::Pair = self
					.ed25519_key_pair(id, &ed25519::Public::from_slice(key.1.as_slice()))
					.ok_or(BareCryptoStoreError::PairNotFound("ed25519".to_owned()))?;
				return Ok(key_pair.sign(msg).encode());
			}
			sr25519::CRYPTO_ID => {
				let key_pair: sr25519::Pair = self
					.sr25519_key_pair(id, &sr25519::Public::from_slice(key.1.as_slice()))
					.ok_or(BareCryptoStoreError::PairNotFound("sr25519".to_owned()))?;
				return Ok(key_pair.sign(msg).encode());
			}
			_ => Err(BareCryptoStoreError::KeyNotSupported(id))
		}
	}
}

/// Macro for exporting functions from wasm in with the expected signature for using it with the
/// wasm executor. This is useful for tests where you need to call a function in wasm.
///
/// The input parameters are expected to be SCALE encoded and will be automatically decoded for you.
/// The output value is also SCALE encoded when returned back to the host.
///
/// The functions are feature-gated with `#[cfg(not(feature = "std"))]`, so they are only available
/// from within wasm.
///
/// # Example
///
/// ```
/// # use sp_core::wasm_export_functions;
///
/// wasm_export_functions! {
///     fn test_in_wasm(value: bool, another_value: Vec<u8>) -> bool {
///         value && another_value.is_empty()
///     }
///
///     fn without_return_value() {
///         // do something
///     }
/// }
/// ```
#[macro_export]
macro_rules! wasm_export_functions {
	(
		$(
			fn $name:ident (
				$( $arg_name:ident: $arg_ty:ty ),* $(,)?
			) $( -> $ret_ty:ty )? { $( $fn_impl:tt )* }
		)*
	) => {
		$(
			$crate::wasm_export_functions! {
				@IMPL
				fn $name (
					$( $arg_name: $arg_ty ),*
				) $( -> $ret_ty )? { $( $fn_impl )* }
			}
		)*
	};
	(@IMPL
		fn $name:ident (
				$( $arg_name:ident: $arg_ty:ty ),*
		) { $( $fn_impl:tt )* }
	) => {
		#[no_mangle]
		#[allow(unreachable_code)]
		#[cfg(not(feature = "std"))]
		pub fn $name(input_data: *mut u8, input_len: usize) -> u64 {
			let input: &[u8] = if input_len == 0 {
				&[0u8; 0]
			} else {
				unsafe {
					$crate::sp_std::slice::from_raw_parts(input_data, input_len)
				}
			};

			{
				let ($( $arg_name ),*) : ($( $arg_ty ),*) = $crate::Decode::decode(
					&mut &input[..],
				).expect("Input data is correctly encoded");

				$( $fn_impl )*
			}

			$crate::to_substrate_wasm_fn_return_value(&())
		}
	};
	(@IMPL
		fn $name:ident (
				$( $arg_name:ident: $arg_ty:ty ),*
		) $( -> $ret_ty:ty )? { $( $fn_impl:tt )* }
	) => {
		#[no_mangle]
		#[allow(unreachable_code)]
		#[cfg(not(feature = "std"))]
		pub fn $name(input_data: *mut u8, input_len: usize) -> u64 {
			let input: &[u8] = if input_len == 0 {
				&[0u8; 0]
			} else {
				unsafe {
					$crate::sp_std::slice::from_raw_parts(input_data, input_len)
				}
			};

			let output $( : $ret_ty )? = {
				let ($( $arg_name ),*) : ($( $arg_ty ),*) = $crate::Decode::decode(
					&mut &input[..],
				).expect("Input data is correctly encoded");

				$( $fn_impl )*
			};

			$crate::to_substrate_wasm_fn_return_value(&output)
		}
	};
}

/// An executor that supports spawning blocking futures in tests.
///
/// Internally this just wraps a `ThreadPool` with a pool size of `8`. This
/// should ensure that we have enough threads in tests for spawning blocking futures.
#[cfg(feature = "std")]
#[derive(Clone)]
pub struct SpawnBlockingExecutor(futures::executor::ThreadPool);

#[cfg(feature = "std")]
impl SpawnBlockingExecutor {
	/// Create a new instance of `Self`.
	pub fn new() -> Self {
		let mut builder = futures::executor::ThreadPoolBuilder::new();
		Self(builder.pool_size(8).create().expect("Failed to create thread pool"))
	}
}

#[cfg(feature = "std")]
impl crate::traits::SpawnBlocking for SpawnBlockingExecutor {
	fn spawn_blocking(&self, _: &'static str, future: futures::future::BoxFuture<'static, ()>) {
		self.0.spawn_ok(future);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::sr25519;
	use crate::testing::{ED25519, SR25519};

	#[test]
	fn store_key_and_extract() {
		let store = KeyStore::new();

		let public = store.write()
			.ed25519_generate_new(ED25519, None)
			.expect("Generates key");

		let public_keys = store.read().keys(ED25519).unwrap();

		assert!(public_keys.contains(&public.into()));
	}

	#[test]
	fn store_unknown_and_extract_it() {
		let store = KeyStore::new();

		let secret_uri = "//Alice";
		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");

		store.write().insert_unknown(
			SR25519,
			secret_uri,
			key_pair.public().as_ref(),
		).expect("Inserts unknown key");

		let public_keys = store.read().keys(SR25519).unwrap();

		assert!(public_keys.contains(&key_pair.public().into()));
	}
}
