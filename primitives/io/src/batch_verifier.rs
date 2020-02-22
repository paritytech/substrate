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

#[derive(Debug, Default)]
pub struct BatchVerifier {
	ed25519_items: Vec<Ed25519BatchItem>,
	sr25519_items: Vec<Sr25519BatchItem>,
}

impl BatchVerifier {
	pub fn new() -> Self {
		Self::default()
	}

	pub fn push_ed25519(
		&mut self,
		signature: ed25519::Signature,
		pub_key: ed25519::Public,
		message: Vec<u8>,
	) {
		self.ed25519_items.push(Ed25519BatchItem { signature, pub_key, message });
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
		// TODO: parallel
		for ed25519_item in self.ed25519_items.drain(..) {
			if !ed25519::Pair::verify(&ed25519_item.signature, &ed25519_item.message, &ed25519_item.pub_key) {
				return false;
			}
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