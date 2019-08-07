// Copyright 2019 Parity Technologies (UK) Ltd.
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

#[cfg(feature = "std")]
use crate::{ed25519, sr25519, crypto::{Public, Pair, KeyTypeId}};

/// A keystore implementation usable in tests.
#[cfg(feature = "std")]
#[derive(Default)]
pub struct KeyStore {
	/// `KeyTypeId` maps to public keys and public keys map to private keys.
	keys: std::collections::HashMap<KeyTypeId, std::collections::HashMap<Vec<u8>, Vec<u8>>>,
}

#[cfg(feature = "std")]
impl KeyStore {
	/// Creates a new instance of `Self`.
	pub fn new() -> std::sync::Arc<parking_lot::RwLock<Self>> {
		std::sync::Arc::new(parking_lot::RwLock::new(Self::default()))
	}
}

#[cfg(feature = "std")]
impl crate::traits::BareCryptoStore for KeyStore {
	fn sr25519_public_keys(&self, id: KeyTypeId) -> Vec<sr25519::Public> {
		self.keys.get(&id)
			.map(|keys|
				keys.values()
					.map(|s| sr25519::Pair::from_seed_slice(s).expect("`sr25519` seed slice is valid"))
					.map(|p| p.public())
					.collect()
			)
			.unwrap_or_default()
	}

	fn sr25519_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<sr25519::Public, String> {
		match seed {
			Some(seed) => {
				let pair = sr25519::Pair::from_string(seed, None).expect("Generates an `sr25519` pair.");
				self.keys.entry(id).or_default().insert(pair.public().to_raw_vec(), pair.to_raw_vec());
				Ok(pair.public())
			},
			None => {
				let (pair, _) = sr25519::Pair::generate();
				self.keys.entry(id).or_default().insert(pair.public().to_raw_vec(), pair.to_raw_vec());
				Ok(pair.public())
			}
		}
	}

	fn sr25519_key_pair(&self, id: KeyTypeId, pub_key: &sr25519::Public) -> Option<sr25519::Pair> {
		self.keys.get(&id)
			.and_then(|inner|
				inner.get(pub_key.as_slice())
					.map(|s| sr25519::Pair::from_seed_slice(s).expect("`sr25519` seed slice is valid"))
			)
	}

	fn ed25519_public_keys(&self, id: KeyTypeId) -> Vec<ed25519::Public> {
		self.keys.get(&id)
			.map(|keys|
				keys.values()
					.map(|s| ed25519::Pair::from_seed_slice(s).expect("`ed25519` seed slice is valid"))
					.map(|p| p.public())
					.collect()
			)
			.unwrap_or_default()
	}

	fn ed25519_generate_new(
		&mut self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<ed25519::Public, String> {
		match seed {
			Some(seed) => {
				let pair = ed25519::Pair::from_string(seed, None).expect("Generates an `ed25519` pair.");
				self.keys.entry(id).or_default().insert(pair.public().to_raw_vec(), pair.to_raw_vec());
				Ok(pair.public())
			},
			None => {
				let (pair, _) = ed25519::Pair::generate();
				self.keys.entry(id).or_default().insert(pair.public().to_raw_vec(), pair.to_raw_vec());
				Ok(pair.public())
			}
		}
	}

	fn ed25519_key_pair(&self, id: KeyTypeId, pub_key: &ed25519::Public) -> Option<ed25519::Pair> {
		self.keys.get(&id)
			.and_then(|inner|
				inner.get(pub_key.as_slice())
					.map(|s| ed25519::Pair::from_seed_slice(s).expect("`ed25519` seed slice is valid"))
			)
	}
}
