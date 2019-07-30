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

//! The best way to understand how this iterator works is to imagine some 2D terrain that have some mountains
//! (digest changes tries) and valleys (changes tries for regular blocks). There are gems (blocks) beneath the
//! terrain. Given the request to find all gems in the range [X1; X2] this iterator will return **minimal set**
//! of points at the terrain (mountains and valleys() inside this range that have to be drilled down to
//! search for gems.

use num_traits::One;
use crate::changes_trie::{ConfigurationRange, BlockNumber};

/// Returns surface iterator for given range of blocks.
pub fn surface_iterator<'a, Number: BlockNumber>(
	config: ConfigurationRange<'a, Number>,
	max: Number,
	begin: Number,
	end: Number,
) -> Result<SurfaceIterator<'a, Number>, String> {
	let (current, current_begin, digest_step, digest_level) = lower_bound_max_digest(
		config.clone(),
		max.clone(),
		begin.clone(),
		end,
	)?;
	Ok(SurfaceIterator {
		config,
		begin,
		max,
		current: Some(current),
		current_begin,
		digest_step,
		digest_level,
	})
}

/// Surface iterator - only traverses top-level digests from given range and tries to find
/// all valid digest changes.
pub struct SurfaceIterator<'a, Number: BlockNumber> {
	config: ConfigurationRange<'a, Number>,
	begin: Number,
	max: Number,
	current: Option<Number>,
	current_begin: Number,
	digest_step: u32,
	digest_level: u32,
}

impl<'a, Number: BlockNumber> Iterator for SurfaceIterator<'a, Number> {
	type Item = Result<(Number, u32), String>;

	fn next(&mut self) -> Option<Self::Item> {
		let current = self.current.clone()?;
		let digest_level = self.digest_level;

		if current < self.digest_step.into() {
			self.current = None;
		} else {
			let next = current.clone() - self.digest_step.into();
			if next.is_zero() || next < self.begin {
				self.current = None;
			} else if next > self.current_begin {
				self.current = Some(next);
			} else {
				let max_digest_interval = lower_bound_max_digest(
					self.config.clone(),
					self.max.clone(),
					self.begin.clone(),
					next,
				);
				let (current, current_begin, digest_step, digest_level) = match max_digest_interval {
					Err(err) => return Some(Err(err)),
					Ok(range) => range,
				};

				self.current = Some(current);
				self.current_begin = current_begin;
				self.digest_step = digest_step;
				self.digest_level = digest_level;
			}
		}

		Some(Ok((current, digest_level)))
	}
}

/// Returns parameters of highest level digest block that includes the end of given range
/// and tends to include the whole range.
fn lower_bound_max_digest<'a, Number: BlockNumber>(
	config: ConfigurationRange<'a, Number>,
	max: Number,
	begin: Number,
	end: Number,
) -> Result<(Number, Number, u32, u32), String> {
	if end > max || begin > end {
		return Err(format!("invalid changes range: {}..{}/{}", begin, end, max));
	}

	let mut digest_level = 0u32;
	let mut digest_step = 1u32;
	let mut digest_interval = 0u32;
	let mut current = end.clone();
	let mut current_begin = begin.clone();
	if current_begin != current {
		while digest_level != config.config.digest_levels {
			let new_digest_level = digest_level + 1;
			let new_digest_step = digest_step * config.config.digest_interval;
			let new_digest_interval = config.config.digest_interval * {
				if digest_interval == 0 { 1 } else { digest_interval }
			};
			let new_digest_begin = config.zero.clone() + ((current.clone() - One::one() - config.zero.clone())
				/ new_digest_interval.into()) * new_digest_interval.into();
			let new_digest_end = new_digest_begin.clone() + new_digest_interval.into();
			let new_current = new_digest_begin.clone() + new_digest_interval.into();

			if new_digest_end > max {
				if begin < new_digest_begin {
					current_begin = new_digest_begin;
				}
				break;
			}

			digest_level = new_digest_level;
			digest_step = new_digest_step;
			digest_interval = new_digest_interval;
			current = new_current;
			current_begin = new_digest_begin;

			if current_begin <= begin && new_digest_end >= end {
				break;
			}
		}
	}

	Ok((
		current,
		current_begin,
		digest_step,
		digest_level,
	))
}

#[cfg(test)]
mod tests {
	use crate::changes_trie::{Configuration};
	use super::*;

	fn configuration_range<'a>(config: &'a Configuration, zero: u64) -> ConfigurationRange<'a, u64> {
		ConfigurationRange {
			config,
			zero,
			end: None,
		}
	}

	#[test]
	fn lower_bound_max_digest_works() {
		let config = Configuration { digest_interval: 4, digest_levels: 2 };

		// when config activates at 0
		assert_eq!(
			lower_bound_max_digest(configuration_range(&config, 0u64), 100_000u64, 20u64, 180u64).unwrap(),
			(192, 176, 16, 2),
		);

		// when config activates at 30
		assert_eq!(
			lower_bound_max_digest(configuration_range(&config, 30u64), 100_000u64, 20u64, 180u64).unwrap(),
			(190, 174, 16, 2),
		);
	}

	#[test]
	fn surface_iterator_works() {
		let config = Configuration { digest_interval: 4, digest_levels: 2 };

		// when config activates at 0
		assert_eq!(
			surface_iterator(configuration_range(&config, 0u64), 100_000u64, 40u64, 180u64).unwrap().collect::<Vec<_>>(),
			vec![
				Ok((192, 2)), Ok((176, 2)), Ok((160, 2)), Ok((144, 2)), Ok((128, 2)), Ok((112, 2)),
				Ok((96, 2)), Ok((80, 2)), Ok((64, 2)), Ok((48, 2)),
			],
		);

		// when config activates at 30
		assert_eq!(
			surface_iterator(configuration_range(&config, 30u64), 100_000u64, 40u64, 180u64).unwrap().collect::<Vec<_>>(),
			vec![
				Ok((190, 2)), Ok((174, 2)), Ok((158, 2)), Ok((142, 2)), Ok((126, 2)), Ok((110, 2)),
				Ok((94, 2)), Ok((78, 2)), Ok((62, 2)), Ok((46, 2)),
			],
		);

		// when config activates at 0 AND max block is before next digest
		assert_eq!(
			surface_iterator(configuration_range(&config, 0u64), 183u64, 40u64, 183u64).unwrap().collect::<Vec<_>>(),
			vec![
				Ok((183, 0)), Ok((182, 0)), Ok((181, 0)), Ok((180, 1)),
				Ok((176, 2)), Ok((160, 2)), Ok((144, 2)), Ok((128, 2)), Ok((112, 2)),
				Ok((96, 2)), Ok((80, 2)), Ok((64, 2)), Ok((48, 2)),
			],
		);
	}

	#[test]
	fn surface_iterator_works_with_skewed_digest() {
	}
}
