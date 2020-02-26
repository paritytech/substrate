// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! This is part of the Substrate runtime.

use sp_core::{ed25519, sr25519, crypto::Pair};
use std::sync::{Arc, atomic::{AtomicBool, AtomicUsize, Ordering as AtomicOrdering}};

#[derive(Debug, Clone)]
struct Ed25519BatchItem {
	signature: ed25519::Signature,
	pub_key: ed25519::Public,
	message: Vec<u8>,
}

#[derive(Debug, Clone)]
struct Sr25519BatchItem {
	signature: sr25519::Signature,
	pub_key: sr25519::Public,
	message: Vec<u8>,
}

#[derive(Debug)]
pub struct BatchVerifier {
	sr25519_items: Vec<Sr25519BatchItem>,
	invalid: Arc<AtomicBool>,
	left: Arc<AtomicUsize>,
}


lazy_static::lazy_static! {
	static ref LOCAL_POOL: futures::executor::ThreadPool = {
		futures::executor::ThreadPool::builder()
			.stack_size(16*1024)
			.name_prefix("io-background")
			.create()
			.expect("failed to create background thread pool")
	};
}

impl BatchVerifier {
	pub fn new() -> Self {
		BatchVerifier {
			sr25519_items: Default::default(),
			invalid: Arc::new(false.into()),
			left: Arc::new(0.into()),
		}
	}

	pub fn push_ed25519(
		&mut self,
		signature: ed25519::Signature,
		pub_key: ed25519::Public,
		message: Vec<u8>,
	) {
		if self.invalid.load(AtomicOrdering::Relaxed) { return; } // there is already invalid transaction encountered

		let invalid_clone = self.invalid.clone();
		let left_clone = self.left.clone();
		self.left.fetch_add(1, AtomicOrdering::SeqCst);

		LOCAL_POOL.spawn_ok(async move {
			if !ed25519::Pair::verify(&signature, &message, &pub_key) {
				invalid_clone.store(true, AtomicOrdering::Relaxed);
			}
			left_clone.fetch_sub(1, AtomicOrdering::SeqCst);
		});
	}

	pub fn push_sr25519(
		&mut self,
		signature: sr25519::Signature,
		pub_key: sr25519::Public,
		message: Vec<u8>,
	) {
		self.sr25519_items.push(Sr25519BatchItem { signature, pub_key, message });
	}

	pub fn verify_and_clear(&mut self) -> bool {
		while self.left.load(AtomicOrdering::SeqCst) != 0 {
			std::thread::park_timeout(std::time::Duration::from_micros(50));
		}

		if self.invalid.load(AtomicOrdering::Relaxed) {
			self.invalid.store(false, AtomicOrdering::Relaxed);
			return false;
		}


		let sr25519_batch_result = {
			let messages = self.sr25519_items.iter().map(|item| &item.message[..]).collect();
			let signatures = self.sr25519_items.iter().map(|item| &item.signature).collect();
			let pub_keys = self.sr25519_items.iter().map(|item| &item.pub_key).collect();

			sr25519::verify_batch(messages, signatures, pub_keys)
		};

		self.sr25519_items.clear();

		sr25519_batch_result
	}
}