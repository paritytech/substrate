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
//! of points at the terrain (mountains and valleys) inside this range that have to be drilled down to
//! search for gems.

use num_traits::One;
use crate::changes_trie::{ConfigurationRange, BlockNumber};

/// Returns surface iterator for given range of blocks.
///
/// `max` is the number of best block, known to caller. We can't access any changes tries
/// that are built after this block, even though we may have them built already.
pub fn surface_iterator<Number: BlockNumber>(
	config: ConfigurationRange<Number>,
	max: Number,
	begin: Number,
	end: Number,
) -> Result<SurfaceIterator<Number>, String> {
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
///
/// Iterator item is the tuple of (last block of the current point + digest level of the current point).
/// Digest level is Some(0) when it is regular block, is Some(non-zero) when it is digest block and None
/// if it is skewed digest block.
pub struct SurfaceIterator<'a, Number: BlockNumber> {
	config: ConfigurationRange<'a, Number>,
	begin: Number,
	max: Number,
	current: Option<Number>,
	current_begin: Number,
	digest_step: u32,
	digest_level: Option<u32>,
}

impl<'a, Number: BlockNumber> Iterator for SurfaceIterator<'a, Number> {
	type Item = Result<(Number, Option<u32>), String>;

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
fn lower_bound_max_digest<Number: BlockNumber>(
	config: ConfigurationRange<Number>,
	max: Number,
	begin: Number,
	end: Number,
) -> Result<(Number, Number, u32, Option<u32>), String> {
	if end > max || begin > end {
		return Err(format!("invalid changes range: {}..{}/{}", begin, end, max));
	}
	if begin <= config.zero || config.end.as_ref().map(|config_end| end > *config_end).unwrap_or(false) {
		return Err(format!("changes trie range is not covered by configuration: {}..{}/{}..{}",
			begin, end, config.zero, match config.end.as_ref() {
				Some(config_end) => format!("{}", config_end),
				None => "None".into(),
			}));
	}

	let mut digest_level = 0u32;
	let mut digest_step = 1u32;
	let mut digest_interval = 0u32;
	let mut current = end.clone();
	let mut current_begin = begin.clone();
	if current_begin != current {
		while digest_level != config.config.digest_levels {
			// try to use next level digest
			let new_digest_level = digest_level + 1;
			let new_digest_step = digest_step * config.config.digest_interval;
			let new_digest_interval = config.config.digest_interval * {
				if digest_interval == 0 { 1 } else { digest_interval }
			};
			let new_digest_begin = config.zero.clone() + ((current.clone() - One::one() - config.zero.clone())
				/ new_digest_interval.into()) * new_digest_interval.into();
			let new_digest_end = new_digest_begin.clone() + new_digest_interval.into();
			let new_current = new_digest_begin.clone() + new_digest_interval.into();

			// check if we met skewed digest
			if let Some(skewed_digest_end) = config.end.as_ref() {
				if new_digest_end > *skewed_digest_end {
					let skewed_digest_start = config.config.prev_max_level_digest_block(
						config.zero.clone(),
						skewed_digest_end.clone(),
					);
					if let Some(skewed_digest_start) = skewed_digest_start {
						let skewed_digest_range = (skewed_digest_end.clone() - skewed_digest_start.clone())
							.try_into().ok()
							.expect("skewed digest range is always <= max level digest range;\
								max level digest range always fits u32; qed");
						return Ok((
							skewed_digest_end.clone(),
							skewed_digest_start,
							skewed_digest_range,
							None,
						));
					}
				}
			}

			// we can't use next level digest if it touches any unknown (> max) blocks
			if new_digest_end > max {
				if begin < new_digest_begin {
					current_begin = new_digest_begin;
				}
				break;
			}

			// we can (and will) use this digest
			digest_level = new_digest_level;
			digest_step = new_digest_step;
			digest_interval = new_digest_interval;
			current = new_current;
			current_begin = new_digest_begin;

			// if current digest covers the whole range => no need to use next level digest
			if current_begin <= begin && new_digest_end >= end {
				break;
			}
		}
	}

	Ok((
		current,
		current_begin,
		digest_step,
		Some(digest_level),
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
			(192, 176, 16, Some(2)),
		);

		// when config activates at 30
		assert_eq!(
			lower_bound_max_digest(configuration_range(&config, 30u64), 100_000u64, 50u64, 210u64).unwrap(),
			(222, 206, 16, Some(2)),
		);
	}

	#[test]
	fn surface_iterator_works() {
		let config = Configuration { digest_interval: 4, digest_levels: 2 };

		// when config activates at 0
		assert_eq!(
			surface_iterator(
				configuration_range(&config, 0u64),
				100_000u64,
				40u64,
				180u64,
			).unwrap().collect::<Vec<_>>(),
			vec![
				Ok((192, Some(2))), Ok((176, Some(2))), Ok((160, Some(2))), Ok((144, Some(2))),
				Ok((128, Some(2))), Ok((112, Some(2))), Ok((96, Some(2))), Ok((80, Some(2))),
				Ok((64, Some(2))), Ok((48, Some(2))),
			],
		);

		// when config activates at 30
		assert_eq!(
			surface_iterator(
				configuration_range(&config, 30u64),
				100_000u64,
				40u64,
				180u64,
			).unwrap().collect::<Vec<_>>(),
			vec![
				Ok((190, Some(2))), Ok((174, Some(2))), Ok((158, Some(2))), Ok((142, Some(2))), Ok((126, Some(2))),
				Ok((110, Some(2))), Ok((94, Some(2))), Ok((78, Some(2))), Ok((62, Some(2))), Ok((46, Some(2))),
			],
		);

		// when config activates at 0 AND max block is before next digest
		assert_eq!(
			surface_iterator(configuration_range(&config, 0u64), 183u64, 40u64, 183u64).unwrap().collect::<Vec<_>>(),
			vec![
				Ok((183, Some(0))), Ok((182, Some(0))), Ok((181, Some(0))), Ok((180, Some(1))),
				Ok((176, Some(2))), Ok((160, Some(2))), Ok((144, Some(2))), Ok((128, Some(2))), Ok((112, Some(2))),
				Ok((96, Some(2))), Ok((80, Some(2))), Ok((64, Some(2))), Ok((48, Some(2))),
			],
		);
	}

	#[test]
	fn surface_iterator_works_with_skewed_digest() {
		let config = Configuration { digest_interval: 4, digest_levels: 2 };
		let mut config_range = configuration_range(&config, 0u64);

		// when config activates at 0 AND ends at 170
		config_range.end = Some(170);
		assert_eq!(
			surface_iterator(config_range, 100_000u64, 40u64, 170u64).unwrap().collect::<Vec<_>>(),
			vec![
				Ok((170, None)), Ok((160, Some(2))), Ok((144, Some(2))), Ok((128, Some(2))), Ok((112, Some(2))),
				Ok((96, Some(2))), Ok((80, Some(2))), Ok((64, Some(2))), Ok((48, Some(2))),
			],
		);
	}
}
