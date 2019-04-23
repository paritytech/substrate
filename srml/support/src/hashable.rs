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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Hashable trait.

use crate::codec::Codec;
use runtime_io::{blake2_128, blake2_256, twox_128, twox_256};
use crate::storage::hashed::generator::StorageHasher;
use crate::Twox64Concat;
use crate::rstd::prelude::Vec;

// This trait must be kept coherent with srml-support-procedural HasherKind usage
pub trait Hashable: Sized {
	fn blake2_128(&self) -> [u8; 16];
	fn blake2_256(&self) -> [u8; 32];
	fn twox_128(&self) -> [u8; 16];
	fn twox_256(&self) -> [u8; 32];
	fn twox_64_concat(&self) -> Vec<u8>;
}

impl<T: Codec> Hashable for T {
	fn blake2_128(&self) -> [u8; 16] {
		self.using_encoded(blake2_128)
	}
	fn blake2_256(&self) -> [u8; 32] {
		self.using_encoded(blake2_256)
	}
	fn twox_128(&self) -> [u8; 16] {
		self.using_encoded(twox_128)
	}
	fn twox_256(&self) -> [u8; 32] {
		self.using_encoded(twox_256)
	}
	fn twox_64_concat(&self) -> Vec<u8> {
		self.using_encoded(Twox64Concat::hash)
	}
}
