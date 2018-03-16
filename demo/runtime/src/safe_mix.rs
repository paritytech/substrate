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

use rstd::ops::{BitAnd, BitOr};
use rstd::cmp;

fn sub_mix<T>(seeds: &[T]) -> T where
	T: BitAnd<Output = T> + BitOr<Output = T> + Copy
{
	(seeds[0] & seeds[1]) | (seeds[1] & seeds[2]) | (seeds[0] & seeds[2])
}

/// 3x3 mixing.
pub fn mix<T>(seeds: &[T]) -> Result<T, ()> where
	T: BitAnd<Output = T> + BitOr<Output = T>,
	T: Default + Copy
{
	Ok(mix_iter(seeds.iter().cloned()))
	/*
	let max_depth = (0..12)
		.scan(1, |a, _| { *a *= 3; Some(*a) })
		.position(|v| seeds.len() == v)
		.ok_or(())?;
	assert!(max_depth <= 11);

	let mut accum = [[T::default(); 3]; 12];
	for i in 0..seeds.len() / 3 {
		// first level:
		accum[0][i % 3] = sub_mix(&seeds[i * 3..i * 3 + 3]);

		let mut index_at_depth = i;
		for depth in 0..12 {
			if index_at_depth % 3 != 2 {
				break;
			}
			index_at_depth /= 3;

			// end of the threesome at depth.
			accum[depth + 1][index_at_depth] = sub_mix(&accum[depth]);
		}
	}
	Ok(accum[max_depth][0])
	*/
}

pub fn mix_iter<T, I>(seeds: I) -> T where
	T: BitAnd<Output = T> + BitOr<Output = T>,
	T: Default + Copy,
	I: Iterator<Item = T>
{
	let mut accum = [[T::default(); 3]; 13];
	let mut max_depth = 0;
	for (i, seed) in seeds.enumerate() {
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
