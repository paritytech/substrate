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

//! # Randomness Module
//!
//! The Randomness module provides a [`random`](./struct.Module.html#method.random) function that
//! generates low-influence random values based on the block hashes from the previous 81 blocks.
//!
//! ## Public Functions
//!
//! See the [`Module`](./struct.Module.html) struct for details of publicly available functions.
//!
//! ## Usage
//!
//! ### Prerequisites
//!
//! Import the Randomness module and derive your module's configuration trait from the system trait.
//!
//! ### Example - Get random seed for the current block
//!
//! ```
//! use support::{decl_module, dispatch::Result};
//!
//! trait Trait: system::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		pub fn random_module_example(origin) -> Result {
//! 			let _random_seed = <srml_random::Module<T>>::random_seed();
//! 			Ok(())
//! 		}
//! 	}
//! }
//! # fn main() { }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::prelude::*;
use sr_primitives::traits::Hash;
use support::{decl_module, decl_storage};
use safe_mix::TripletMix;
use codec::Encode;
use system::Trait;

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn on_initialize() {
			let parent_hash = <system::Module<T>>::parent_hash();

			<RandomMaterial<T>>::mutate(|&mut(ref mut index, ref mut values)| if values.len() < 81 {
				values.push(parent_hash)
			} else {
				values[*index as usize] = parent_hash;
				*index = (*index + 1) % 81;
			});
		}
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as System {
		/// Series of block headers from the last 81 blocks that acts as random seed material. This is arranged as a
		/// ring buffer with the `i8` prefix being the index into the `Vec` of the oldest hash.
		RandomMaterial get(random_material): (i8, Vec<T::Hash>);
	}
}

impl<T: Trait> Module<T> {
	/// Get the basic random seed.
	///
	/// In general you won't want to use this, but rather `Self::random` which
	/// allows you to give a subject for the random result and whose value will
	/// be independently low-influence random from any other such seeds.
	pub fn random_seed() -> T::Hash {
		Self::random(&[][..])
	}

	/// Get a low-influence "random" value.
	///
	/// Being a deterministic block chain, real randomness is difficult to come
	/// by. This gives you something that approximates it. `subject` is a
	/// context identifier and allows you to get a different result to other
	/// callers of this function; use it like `random(&b"my context"[..])`.
	///
	/// This is initially implemented through a low-influence "triplet mix"
	/// convolution of previous block hash values. In the future it will be
	/// generated from a secure verifiable random function (VRF).
	///
	/// ### Security Notes
	///
	/// This randomness uses a low-influence function, drawing upon the block
	/// hashes from the previous 81 blocks. Its result for any given subject
	/// will be known in advance by the block producer of this block (and,
	/// indeed, anyone who knows the block's `parent_hash`). However, it is
	/// mostly impossible for the producer of this block *alone* to influence
	/// the value of this hash. A sizable minority of dishonest and coordinating
	/// block producers would be required in order to affect this value. If that
	/// is an insufficient security guarantee then two things can be used to
	/// improve this randomness:
	///
	/// - Name, in advance, the block number whose random value will be used;
	///   ensure your module retains a buffer of previous random values for its
	///   subject and then index into these in order to obviate the ability of
	///   your user to look up the parent hash and choose when to transact based
	///   upon it.
	/// - Require your user to first commit to an additional value by first
	///   posting its hash. Require them to reveal the value to determine the
	///   final result, hashing it with the output of this random function. This
	///   reduces the ability of a cabal of block producers from conspiring
	///   against individuals.
	///
	/// WARNING: Hashing the result of this function will remove any
	/// low-influence properties it has and mean that all bits of the resulting
	/// value are entirely manipulatable by the author of the parent block, who
	/// can determine the value of `parent_hash`.
	pub fn random(subject: &[u8]) -> T::Hash {
		let (index, hash_series) = <RandomMaterial<T>>::get();
		if hash_series.len() > 0 {
			// Always the case after block 1 is initialised.
			hash_series.iter()
				.cycle()
				.skip(index as usize)
				.take(81)
				.enumerate()
				.map(|(i, h)| (i as i8, subject, h).using_encoded(T::Hashing::hash))
				.triplet_mix()
		} else {
			T::Hash::default()
		}
	}
}
