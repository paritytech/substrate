// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Types that should only be used for testing!

use crate::crypto::KeyTypeId;
#[cfg(feature = "std")]
use crate::{
	crypto::{Pair, Public, CryptoTypePublicPair},
	ed25519, sr25519, ecdsa,
	traits::Error,
	vrf::{VRFTranscriptData, VRFSignature, make_transcript},
};
#[cfg(feature = "std")]
use std::collections::HashSet;

/// Key type for generic Ed25519 key.
pub const ED25519: KeyTypeId = KeyTypeId(*b"ed25");
/// Key type for generic Sr 25519 key.
pub const SR25519: KeyTypeId = KeyTypeId(*b"sr25");
/// Key type for generic Sr 25519 key.
pub const ECDSA: KeyTypeId = KeyTypeId(*b"ecds");

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

	fn ecdsa_key_pair(&self, id: KeyTypeId, pub_key: &ecdsa::Public) -> Option<ecdsa::Pair> {
		self.keys.get(&id)
			.and_then(|inner|
				inner.get(pub_key.as_slice())
					.map(|s| ecdsa::Pair::from_string(s, None).expect("`ecdsa` seed slice is valid"))
			)
	}

}

#[cfg(feature = "std")]
impl crate::traits::BareCryptoStore for KeyStore {
	fn keys(&self, id: KeyTypeId) -> Result<Vec<CryptoTypePublicPair>, Error> {
		self.keys
			.get(&id)
			.map(|map| {
				Ok(map.keys()
					.fold(Vec::new(), |mut v, k| {
						v.push(CryptoTypePublicPair(sr25519::CRYPTO_ID, k.clone()));
						v.push(CryptoTypePublicPair(ed25519::CRYPTO_ID, k.clone()));
						v.push(CryptoTypePublicPair(ecdsa::CRYPTO_ID, k.clone()));
						v
					}))
			})
			.unwrap_or_else(|| Ok(vec![]))
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
	) -> Result<sr25519::Public, Error> {
		match seed {
			Some(seed) => {
				let pair = sr25519::Pair::from_string(seed, None)
					.map_err(|_| Error::ValidationError("Generates an `sr25519` pair.".to_owned()))?;
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
	) -> Result<ed25519::Public, Error> {
		match seed {
			Some(seed) => {
				let pair = ed25519::Pair::from_string(seed, None)
					.map_err(|_| Error::ValidationError("Generates an `ed25519` pair.".to_owned()))?;
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

	fn ecdsa_public_keys(&self, id: KeyTypeId) -> Vec<ecdsa::Public> {
		self.keys.get(&id)
			.map(|keys|
				keys.values()
					.map(|s| ecdsa::Pair::from_string(s, None).expect("`ecdsa` seed slice is valid"))
					.map(|p| p.public())
					.collect()
			)
			.unwrap_or_default()
	}

	fn ecdsa_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<ecdsa::Public, Error> {
		match seed {
			Some(seed) => {
				let pair = ecdsa::Pair::from_string(seed, None)
					.map_err(|_| Error::ValidationError("Generates an `ecdsa` pair.".to_owned()))?;
				self.keys.entry(id).or_default().insert(pair.public().to_raw_vec(), seed.into());
				Ok(pair.public())
			},
			None => {
				let (pair, phrase, _) = ecdsa::Pair::generate_with_phrase(None);
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
	) -> std::result::Result<Vec<CryptoTypePublicPair>, Error> {
		let provided_keys = keys.into_iter().collect::<HashSet<_>>();
		let all_keys = self.keys(id)?.into_iter().collect::<HashSet<_>>();

		Ok(provided_keys.intersection(&all_keys).cloned().collect())
	}

	fn sign_with(
		&self,
		id: KeyTypeId,
		key: &CryptoTypePublicPair,
		msg: &[u8],
	) -> Result<Vec<u8>, Error> {
		use codec::Encode;

		match key.0 {
			ed25519::CRYPTO_ID => {
				let key_pair: ed25519::Pair = self
					.ed25519_key_pair(id, &ed25519::Public::from_slice(key.1.as_slice()))
					.ok_or_else(|| Error::PairNotFound("ed25519".to_owned()))?;
				return Ok(key_pair.sign(msg).encode());
			}
			sr25519::CRYPTO_ID => {
				let key_pair: sr25519::Pair = self
					.sr25519_key_pair(id, &sr25519::Public::from_slice(key.1.as_slice()))
					.ok_or_else(|| Error::PairNotFound("sr25519".to_owned()))?;
				return Ok(key_pair.sign(msg).encode());
			}
			ecdsa::CRYPTO_ID => {
				let key_pair: ecdsa::Pair = self
					.ecdsa_key_pair(id, &ecdsa::Public::from_slice(key.1.as_slice()))
					.ok_or_else(|| Error::PairNotFound("ecdsa".to_owned()))?;
				return Ok(key_pair.sign(msg).encode());
			}
			_ => Err(Error::KeyNotSupported(id))
		}
	}

	fn sr25519_vrf_sign(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		transcript_data: VRFTranscriptData,
	) -> Result<VRFSignature, Error> {
		let transcript = make_transcript(transcript_data);
		let pair = self.sr25519_key_pair(key_type, public)
			.ok_or_else(|| Error::PairNotFound("Not found".to_owned()))?;

		let (inout, proof, _) = pair.as_ref().vrf_sign(transcript);
		Ok(VRFSignature {
			output: inout.to_output(),
			proof,
		})
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
impl crate::traits::SpawnNamed for SpawnBlockingExecutor {
	fn spawn_blocking(&self, _: &'static str, future: futures::future::BoxFuture<'static, ()>) {
		self.0.spawn_ok(future);
	}
	fn spawn(&self, _: &'static str, future: futures::future::BoxFuture<'static, ()>) {
		self.0.spawn_ok(future);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::sr25519;
	use crate::testing::{ED25519, SR25519};
	use crate::vrf::VRFTranscriptValue;

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

	#[test]
	fn vrf_sign() {
		let store = KeyStore::new();

		let secret_uri = "//Alice";
		let key_pair = sr25519::Pair::from_string(secret_uri, None).expect("Generates key pair");

		let transcript_data = VRFTranscriptData {
			label: b"Test",
			items: vec![
				("one", VRFTranscriptValue::U64(1)),
				("two", VRFTranscriptValue::U64(2)),
				("three", VRFTranscriptValue::Bytes("test".as_bytes())),
			]
		};

		let result = store.read().sr25519_vrf_sign(
			SR25519,
			&key_pair.public(),
			transcript_data.clone(),
		);
		assert!(result.is_err());

		store.write().insert_unknown(
			SR25519,
			secret_uri,
			key_pair.public().as_ref(),
		).expect("Inserts unknown key");

		let result = store.read().sr25519_vrf_sign(
			SR25519,
			&key_pair.public(),
			transcript_data,
		);

		assert!(result.is_ok());
	}
}
