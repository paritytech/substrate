// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! A simple pseudo random number generator that allows a stream of random numbers to be efficiently
//! created from a single initial seed hash.

use codec::{Encode, Decode};
use crate::traits::{Hash, TrailingZeroInput};

/// Pseudo-random number streamer. This retains the state of the random number stream. It's as
/// secure as the combination of the seed with which it is constructed and the hash function it uses
/// to cycle elements.
///
/// It can be saved and later reloaded using the Codec traits.
///
/// (It is recommended to use the `rand_chacha` crate as an alternative to this where possible.)
///
/// Example:
/// ```
/// use sp_runtime::traits::{Hash, BlakeTwo256};
/// use sp_runtime::RandomNumberGenerator;
/// let random_seed = BlakeTwo256::hash(b"Sixty-nine");
/// let mut rng = <RandomNumberGenerator<BlakeTwo256>>::new(random_seed);
/// assert_eq!(rng.pick_u32(100), 59);
/// assert_eq!(rng.pick_item(&[1, 2, 3]), Some(&1));
/// ```
///
/// This can use any cryptographic `Hash` function as the means of entropy-extension, and avoids
/// needless extensions of entropy.
///
/// If you're persisting it over blocks, be aware that the sequence will start to repeat. This won't
/// be a practical issue unless you're using tiny hash types (e.g. 64-bit) and pulling hundred of
/// megabytes of data from it.
#[derive(Encode, Decode)]
pub struct RandomNumberGenerator<Hashing: Hash> {
	current: Hashing::Output,
	offset: u32,
}

impl<Hashing: Hash> RandomNumberGenerator<Hashing> {
	/// A new source of random data.
	pub fn new(seed: Hashing::Output) -> Self {
		Self {
			current: seed,
			offset: 0,
		}
	}

	fn offset(&self) -> usize { self.offset as usize }

	/// Returns a number at least zero, at most `max`.
	pub fn pick_u32(&mut self, max: u32) -> u32 {
		let needed = (4 - max.leading_zeros() / 8) as usize;
		let top = ((1 << (needed as u64 * 8)) / (max as u64 + 1) * (max as u64 + 1) - 1) as u32;
		loop {
			if self.offset() + needed > self.current.as_ref().len() {
				// rehash
				self.current = <Hashing as Hash>::hash(self.current.as_ref());
				self.offset = 0;
			}
			let data = &self.current.as_ref()[self.offset()..self.offset() + needed];
			self.offset += needed as u32;
			let raw = u32::decode(&mut TrailingZeroInput::new(data)).unwrap_or(0);
			if raw <= top {
				break if max < u32::max_value() {
					raw % (max + 1)
				} else {
					raw
				}
			}
		}
	}

	/// Returns a number at least zero, at most `max`.
	///
	/// This returns a `usize`, but internally it only uses `u32` so avoid consensus problems.
	pub fn pick_usize(&mut self, max: usize) -> usize {
		self.pick_u32(max as u32) as usize
	}

	/// Pick a random element from an array of `items`.
	///
	/// This is guaranteed to return `Some` except in the case that the given array `items` is
	/// empty.
	pub fn pick_item<'a, T>(&mut self, items: &'a [T]) -> Option<&'a T> {
		if items.is_empty() {
			None
		} else {
			Some(&items[self.pick_usize(items.len() - 1)])
		}
	}
}

#[cfg(test)]
mod tests {
	use super::RandomNumberGenerator;
	use crate::traits::{Hash, BlakeTwo256};

	#[test]
	fn does_not_panic_on_max() {
		let seed = BlakeTwo256::hash(b"Fourty-two");
		let _random = RandomNumberGenerator::<BlakeTwo256>::new(seed).pick_u32(u32::MAX);
	}
}
