// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! Session key store is an in memory key store.

#![warn(missing_docs)]

use parking_lot::Mutex;
use substrate_primitives::crypto::{KeyTypeId, Pair};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

// 24h in seconds
const INACTIVITY_PERIOD: u64 = 60 * 60 * 24;

/// Keystore error.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Invalid seed
	#[display(fmt="Invalid seed")]
	InvalidSeed,
}

impl std::error::Error for Error {}

/// Keystore Result
pub type Result<T> = std::result::Result<T, Error>;

/// Handler for `Store` events.
trait StoreHandler: Send {
	/// Called when a new session key is added to the store.
	fn on_add_session_key(&mut self, pair: &[u8]);
}

/// Store for session keys.
pub struct Store {
	handlers: Mutex<Vec<(KeyTypeId, Box<dyn StoreHandler>)>>,
}

impl Store {
	/// Create a new store.
	pub fn new() -> Self {
		Self {
			handlers: Default::default(),
		}
	}

	/// Adds a session key pair.
	pub fn add_key<TPair: Pair>(&self, pair: &TPair) {
		let value = pair.to_raw_vec();
		let mut handlers = self.handlers.lock();
		for (key_type, handler) in handlers.iter_mut() {
			if *key_type == TPair::KEY_TYPE {
				handler.on_add_session_key(&value[..]);
			}
		}
	}

	/// Adds a session key pair from a seed. Used for testing.
	pub fn add_key_from_seed<TPair: Pair>(&self, seed: &str) -> Result<()> {
		let pair = TPair::from_string(seed, None)
			.map_err(|_| Error::InvalidSeed)?;
		self.add_key(&pair);
		Ok(())
	}

	/// Creates a local session store.
	pub fn create_local_store<TPair>(&self) -> Arc<LocalStore<TPair>>
	where
		TPair: Pair + Send + Clone,
		TPair::Public: Send + Clone,
	{
		let session_store = Arc::new(LocalStore::new());
		self.handlers.lock().push((TPair::KEY_TYPE, Box::new(session_store.clone())));
		session_store
	}
}

/// A local session store supporting a single crypto algorithm.
pub struct LocalStore<TPair: Pair> {
	keys: Mutex<HashMap<TPair::Public, (TPair, Instant)>>,
}

impl<TPair> LocalStore<TPair>
where
	TPair: Pair + Send + Clone,
	TPair::Public: Send + Clone,
{
	/// Creates a new `LocalStore`.
	pub fn new() -> Self {
		Self {
			keys: Default::default(),
		}
	}

	/// Gets the key matching the public key.
	pub fn get_key(&self, public: &TPair::Public) -> Option<TPair> {
		let pair = {
			let mut keys = self.keys.lock();
			if let Some(value) = keys.get_mut(public) {
				value.1 = Instant::now();
				Some(value.0.clone())
			} else {
				None
			}
		};
		self.clean();
		pair
	}

	/// Find keys matching a predicate.
	pub fn get_keys(&self, f: impl Fn(&TPair::Public) -> bool) -> Vec<TPair> {
		let filtered_keys = {
			self.keys.lock().iter_mut()
				.filter(|(public, _)| f(public))
				.map(|(_, value)| {
					value.1 = Instant::now();
					value.0.clone()
				})
				.collect::<Vec<_>>()
		};
		self.clean();
		filtered_keys
	}

	/// Cleanup session store.
	fn clean(&self) {
		let mut keys = self.keys.lock();
		if keys.len() > 1 {
			let duration = Duration::new(INACTIVITY_PERIOD, 0);
			let new_keys = keys.iter().filter(|(_, (_, instant))| {
				Instant::now().duration_since(instant.clone()) < duration
			}).map(|(k, v)| (k.clone(), v.clone())).collect::<HashMap<_, _>>();
			// If a validator gets unstaked but then restaked some sessions later
			// prevent the validator from getting slashed.
			if new_keys.len() > 0 {
				*keys = new_keys;
			}
		}
	}
}

impl<TPair> StoreHandler for Arc<LocalStore<TPair>>
where
	TPair: Pair + Send,
	TPair::Public: Send,
{
	fn on_add_session_key(&mut self, pair: &[u8]) {
		let pair = TPair::from_seed_slice(pair)
			.expect("store contains valid bytes");
		let mut keys = self.keys.lock();
		keys.insert(pair.public(), (pair, Instant::now()));
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_primitives::ed25519;

	#[test]
	fn test_handler() {
		let store = Store::new();
		let local_store = store.create_local_store::<ed25519::Pair>();

		let key_a1 = ed25519::Pair::from_seed(&[0; 32]);
		let key_b1 = ed25519::Pair::from_string("//Alice", None).unwrap();
		store.add_key(&key_a1);
		store.add_key_from_seed::<ed25519::Pair>("//Alice").unwrap();
		let key_a2 = local_store.get_key(&key_a1.public()).unwrap();
		let key_b2 = local_store.get_key(&key_b1.public()).unwrap();
		assert_eq!(key_a1.to_raw_vec(), key_a2.to_raw_vec());
		assert_eq!(key_b1.to_raw_vec(), key_b2.to_raw_vec());
	}
}
