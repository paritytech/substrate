// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Means of mixing a series of hashes to create a single secure hash.
//!
//! Described in http://www.cs.huji.ac.il/~nati/PAPERS/coll_coin_fl.pdf

use rstd::ops::{BitAnd, BitOr};
use rstd::cmp;

fn sub_mix<T>(seeds: &[T]) -> T where
	T: BitAnd<Output = T> + BitOr<Output = T> + Copy
{
	(seeds[0] & seeds[1]) | (seeds[1] & seeds[2]) | (seeds[0] & seeds[2])
}

/// Mix a slice.
pub fn mix<T>(seeds: &[T]) -> Result<T, ()> where
	T: BitAnd<Output = T> + BitOr<Output = T>,
	T: Default + Copy
{
	Ok(seeds.iter().cloned().mixed())
}

/// The mixed trait for mixing a ssequence.
pub trait Mixed {
	/// The items in the sequence and simultaneously the return of the mixing.
	type Item;
	/// The output of the mixing algorithm on the sequence.
	fn mixed(self) -> Self::Item;
}

impl<I, T> Mixed for I where
	I: Iterator<Item = T>,
	T: BitAnd<Output = T> + BitOr<Output = T> + Default + Copy
{
	type Item = T;
	fn mixed(self) -> Self::Item {
		let mut accum = [[T::default(); 3]; 13];
		let mut max_depth = 0;
		for (i, seed) in self.enumerate() {
			accum[0][i % 3] = seed;
			let mut index_at_depth = i;
			for depth in 0..13 {
				if index_at_depth % 3 != 2 {
					break;
				}
				index_at_depth /= 3;

				// end of the threesome at depth.
				accum[depth + 1][index_at_depth % 3] = sub_mix(&accum[depth]);
				max_depth = cmp::max(max_depth, depth + 1);
				if max_depth == 12 {
					break;
				}
			}
		}
		accum[max_depth][0]
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn sub_mix_works() {
		assert_eq!(sub_mix(&[0, 0, 0][..]), 0);
		assert_eq!(sub_mix(&[0, 0, 1][..]), 0);
		assert_eq!(sub_mix(&[0, 1, 0][..]), 0);
		assert_eq!(sub_mix(&[0, 1, 1][..]), 1);
		assert_eq!(sub_mix(&[1, 0, 0][..]), 0);
		assert_eq!(sub_mix(&[1, 0, 1][..]), 1);
		assert_eq!(sub_mix(&[1, 1, 0][..]), 1);
		assert_eq!(sub_mix(&[1, 1, 1][..]), 1);

		assert_eq!(sub_mix(&[0, 0, 0][..]), 0);
		assert_eq!(sub_mix(&[0, 0, 2][..]), 0);
		assert_eq!(sub_mix(&[0, 2, 0][..]), 0);
		assert_eq!(sub_mix(&[0, 2, 2][..]), 2);
		assert_eq!(sub_mix(&[2, 0, 0][..]), 0);
		assert_eq!(sub_mix(&[2, 0, 2][..]), 2);
		assert_eq!(sub_mix(&[2, 2, 0][..]), 2);
		assert_eq!(sub_mix(&[2, 2, 2][..]), 2);
	}

	#[test]
	fn mix_works_on_first_level() {
		assert_eq!(mix(&[0, 0, 0][..]).unwrap(), 0);
		assert_eq!(mix(&[0, 0, 1][..]).unwrap(), 0);
		assert_eq!(mix(&[0, 1, 0][..]).unwrap(), 0);
		assert_eq!(mix(&[0, 1, 1][..]).unwrap(), 1);
		assert_eq!(mix(&[1, 0, 0][..]).unwrap(), 0);
		assert_eq!(mix(&[1, 0, 1][..]).unwrap(), 1);
		assert_eq!(mix(&[1, 1, 0][..]).unwrap(), 1);
		assert_eq!(mix(&[1, 1, 1][..]).unwrap(), 1);

		assert_eq!(mix(&[0, 0, 0][..]).unwrap(), 0);
		assert_eq!(mix(&[0, 0, 2][..]).unwrap(), 0);
		assert_eq!(mix(&[0, 2, 0][..]).unwrap(), 0);
		assert_eq!(mix(&[0, 2, 2][..]).unwrap(), 2);
		assert_eq!(mix(&[2, 0, 0][..]).unwrap(), 0);
		assert_eq!(mix(&[2, 0, 2][..]).unwrap(), 2);
		assert_eq!(mix(&[2, 2, 0][..]).unwrap(), 2);
		assert_eq!(mix(&[2, 2, 2][..]).unwrap(), 2);
	}

	#[test]
	fn mix_works_on_second_level() {
		assert_eq!(mix(&[0, 0, 0, 0, 0, 1, 0, 1, 0][..]).unwrap(), 0);
		assert_eq!(mix(&[0, 1, 1, 1, 0, 0, 1, 0, 1][..]).unwrap(), 1);
		assert_eq!(mix(&[1, 1, 0, 1, 1, 1, 0, 0, 0][..]).unwrap(), 1);
	}

	#[test]
	fn mix_works_on_third_level() {
		assert_eq!(mix(&[0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0][..]).unwrap(), 1);
	}
}
