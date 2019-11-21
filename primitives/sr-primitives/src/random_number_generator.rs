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

//! A simple random number generator that allows a stream of random numbers to be efficiently
//! created from a single initial seed hash.

use codec::{Encode, Decode};
use crate::traits::{Hash, TrailingZeroInput};

/// Random number streamer. This retains the state of the random number stream.
///
/// It can be saved and later reloaded using the Codec traits.
///
/// Example:
/// ```
/// use sr_primitives::traits::{Hash, BlakeTwo256};
/// use sr_primitives::RandomNumberGenerator;
/// let random_seed = BlakeTwo256::hash(b"Sixty-nine");
/// let mut rng = <RandomNumberGenerator<BlakeTwo256>>::new(random_seed);
/// assert_eq!(rng.pick_u32(100), 47);
/// assert_eq!(rng.pick_item(&[1, 2, 3]), Some(&2));
/// ```
///
/// This can use any cryptographic `Hash` function as the means of entropy-extension, and avoids
/// needless extensions of entropy.
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
		if self.offset() + needed > self.current.as_ref().len() {
			// rehash
			self.current = Hashing::hash(self.current.as_ref());
			self.offset = 0;
		}
		let data = &self.current.as_ref()[self.offset()..self.offset() + needed];
		self.offset += needed as u32;
		let raw = u32::decode(&mut TrailingZeroInput::new(data)).unwrap_or(0);
		if max < u32::max_value() {
			raw % (max + 1)
		} else {
			raw
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
