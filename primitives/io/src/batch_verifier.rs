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

use sp_core::{ed25519, crypto::Pair};

#[derive(Debug, Clone)]
struct Ed25519BatchItem {
	sig: ed25519::Signature,
	pub_key: ed25519::Public,
	message: Vec<u8>,
}

#[derive(Debug, Default)]
pub struct BatchVerifier {
	ed25519_items: Vec<Ed25519BatchItem>,
}

impl BatchVerifier {
	pub fn new() -> Self {
		Self::default()
	}

	pub fn push_ed25519(
		&mut self,
		sig: ed25519::Signature,
		pub_key: ed25519::Public,
		message: Vec<u8>)
	{
		self.ed25519_items.push(Ed25519BatchItem { sig, pub_key, message });
	}

	pub fn verify_and_clear(&mut self) -> bool {
		for ed25519_item in self.ed25519_items.drain(..) {
			if !ed25519::Pair::verify(&ed25519_item.sig, &ed25519_item.message, &ed25519_item.pub_key) {
				return false;
			}
		}

		true
	}
}