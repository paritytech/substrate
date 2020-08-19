// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! # Merkle Mountain Range
//!
//! ## Overview
//!
#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	debug,
	decl_module, decl_storage,
	weights::Weight,
};

#[cfg(test)]
mod tests;

/// This pallet's configuration trait
pub trait Trait: frame_system::Trait {

}

decl_storage! {
	trait Store for Module<T: Trait> as MerkleMountainRange {
	}
}

decl_module! {
	/// A public part of the pallet.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn on_initialize(block_number: T::BlockNumber) -> Weight {
			debug::native::info!("Hello World from offchain workers!");
			todo!()
		}
	}
}
impl<T: Trait> Module<T> {
}

