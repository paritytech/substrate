// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
