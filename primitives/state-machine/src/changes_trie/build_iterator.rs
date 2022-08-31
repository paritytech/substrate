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

//! Structures and functions to return blocks whose changes are to be included
//! in given block's changes trie.

use num_traits::Zero;
use crate::changes_trie::{ConfigurationRange, BlockNumber};

/// Returns iterator of OTHER blocks that are required for inclusion into
/// changes trie of given block. Blocks are guaranteed to be returned in
/// ascending order.
///
/// Skewed digest is built IF block >= config.end.
pub fn digest_build_iterator<'a, Number: BlockNumber>(
	config: ConfigurationRange<'a, Number>,
	block: Number,
) -> DigestBuildIterator<Number> {
	// prepare digest build parameters
	let (_, _, digest_step) = match config.config.digest_level_at_block(config.zero, block.clone()) {
		Some((current_level, digest_interval, digest_step)) =>
			(current_level, digest_interval, digest_step),
		None => return DigestBuildIterator::empty(),
	};

	DigestBuildIterator::new(block.clone(), config.end.unwrap_or(block), config.config.digest_interval, digest_step)
}

/// Changes trie build iterator that returns numbers of OTHER blocks that are
/// required for inclusion into changes trie of given block.
#[derive(Debug)]
pub struct DigestBuildIterator<Number: BlockNumber> {
	/// Block we're building changes trie for. It could (logically) be a post-end block if we are creating
	/// skewed digest.
	block: Number,
	/// Block that is a last block where current configuration is active. We have never yet created anything
	/// after this block => digest that we're creating can't reference any blocks that are >= end.
	end: Number,
	/// Interval of L1 digest blocks.
	digest_interval: u32,
	/// Max step that could be used when digest is created.
	max_step: u32,

	// Mutable data below:

	/// Step of current blocks range.
	current_step: u32,
	/// Reverse step of current blocks range.
	current_step_reverse: u32,
	/// Current blocks range.
	current_range: Option<BlocksRange<Number>>,
	/// Last block that we have returned.
	last_block: Option<Number>,
}

impl<Number: BlockNumber> DigestBuildIterator<Number> {
	/// Create new digest build iterator.
	pub fn new(block: Number, end: Number, digest_interval: u32, max_step: u32) -> Self {
		DigestBuildIterator {
			block,
			end,
			digest_interval,
			max_step,
			current_step: max_step,
			current_step_reverse: 0,
			current_range: None,
			last_block: None,
		}
	}

	/// Create empty digest build iterator.
	pub fn empty() -> Self {
		Self::new(Zero::zero(), Zero::zero(), 0, 0)
	}
}

impl<Number: BlockNumber> Iterator for DigestBuildIterator<Number> {
	type Item = Number;

	fn next(&mut self) -> Option<Self::Item> {
		// when we're building skewed digest, we might want to skip some blocks if
		// they're not covered by current configuration
		loop {
			if let Some(next) = self.current_range.as_mut().and_then(|iter| iter.next()) {
				if next < self.end {
					self.last_block = Some(next.clone());
					return Some(next);
				}
			}

			// we are safe to use non-checking mul/sub versions here because:
			// DigestBuildIterator is created only by internal function that is checking
			// that all multiplications/subtractions are safe within max_step limit

			let next_step_reverse = if self.current_step_reverse == 0 {
				1
			} else {
				self.current_step_reverse * self.digest_interval
			};
			if next_step_reverse > self.max_step {
				return None;
			}

			self.current_step_reverse = next_step_reverse;
			self.current_range = Some(BlocksRange::new(
				match self.last_block.clone() {
					Some(last_block) => last_block + self.current_step.into(),
					None => self.block.clone() - (self.current_step * self.digest_interval - self.current_step).into(),
				},
				self.block.clone(),
				self.current_step.into(),
			));

			self.current_step = self.current_step / self.digest_interval;
			if self.current_step == 0 {
				self.current_step = 1;
			}
		}
	}
}

/// Blocks range iterator with builtin step_by support.
#[derive(Debug)]
struct BlocksRange<Number: BlockNumber> {
	current: Number,
	end: Number,
	step: Number,
}

impl<Number: BlockNumber> BlocksRange<Number> {
	pub fn new(begin: Number, end: Number, step: Number) -> Self {
		BlocksRange {
			current: begin,
			end,
			step,
		}
	}
}

impl<Number: BlockNumber> Iterator for BlocksRange<Number> {
	type Item = Number;

	fn next(&mut self) -> Option<Self::Item> {
		if self.current >= self.end {
			return None;
		}

		let current = Some(self.current.clone());
		self.current += self.step.clone();
		current
	}
}

#[cfg(test)]
mod tests {
	use crate::changes_trie::Configuration;
	use super::*;

	fn digest_build_iterator(
		digest_interval: u32,
		digest_levels: u32,
		zero: u64,
		block: u64,
		end: Option<u64>,
	) -> DigestBuildIterator<u64> {
		super::digest_build_iterator(
			ConfigurationRange {
				config: &Configuration {
					digest_interval,
					digest_levels,
				},
				zero,
				end,
			},
			block,
		)
	}

	fn digest_build_iterator_basic(
		digest_interval: u32,
		digest_levels: u32,
		zero: u64,
		block: u64,
	) -> (u64, u32, u32) {
		let iter = digest_build_iterator(digest_interval, digest_levels, zero, block, None);
		(iter.block, iter.digest_interval, iter.max_step)
	}

	fn digest_build_iterator_blocks(
		digest_interval: u32,
		digest_levels: u32,
		zero: u64,
		block: u64,
		end: Option<u64>,
	) -> Vec<u64> {
		digest_build_iterator(digest_interval, digest_levels, zero, block, end).collect()
	}

	#[test]
	fn suggest_digest_inclusion_returns_empty_iterator() {
		fn test_with_zero(zero: u64) {
			let empty = (0, 0, 0);
			assert_eq!(digest_build_iterator_basic(4, 16, zero, zero + 0), empty, "block is 0");
			assert_eq!(digest_build_iterator_basic(0, 16, zero, zero + 64), empty, "digest_interval is 0");
			assert_eq!(digest_build_iterator_basic(1, 16, zero, zero + 64), empty, "digest_interval is 1");
			assert_eq!(digest_build_iterator_basic(4, 0, zero, zero + 64), empty, "digest_levels is 0");
			assert_eq!(
				digest_build_iterator_basic(4, 16, zero, zero + 1),
				empty,
				"digest is not required for this block",
			);
			assert_eq!(
				digest_build_iterator_basic(4, 16, zero, zero + 2),
				empty,
				"digest is not required for this block",
			);
			assert_eq!(
				digest_build_iterator_basic(4, 16, zero, zero + 15),
				empty,
				"digest is not required for this block",
			);
			assert_eq!(
				digest_build_iterator_basic(4, 16, zero, zero + 17),
				empty,
				"digest is not required for this block",
			);
			assert_eq!(digest_build_iterator_basic(
				::std::u32::MAX / 2 + 1,
				16,
				zero,
				::std::u64::MAX,
			), empty, "digest_interval * 2 is greater than u64::MAX");
		}

		test_with_zero(0);
		test_with_zero(1);
		test_with_zero(2);
		test_with_zero(4);
		test_with_zero(17);
	}

	#[test]
	fn suggest_digest_inclusion_returns_level1_iterator() {
		fn test_with_zero(zero: u64) {
			assert_eq!(
				digest_build_iterator_basic(16, 1, zero, zero + 16),
				(zero + 16, 16, 1),
				"!(block % interval) && first digest level == block",
			);
			assert_eq!(
				digest_build_iterator_basic(16, 1, zero, zero + 256),
				(zero + 256, 16, 1),
				"!(block % interval^2), but there's only 1 digest level",
			);
			assert_eq!(
				digest_build_iterator_basic(16, 2, zero, zero + 32),
				(zero + 32, 16, 1),
				"second level digest is not required for this block",
			);
			assert_eq!(
				digest_build_iterator_basic(16, 3, zero, zero + 4080),
				(zero + 4080, 16, 1),
				"second && third level digest are not required for this block",
			);
		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn suggest_digest_inclusion_returns_level2_iterator() {
		fn test_with_zero(zero: u64) {
			assert_eq!(
				digest_build_iterator_basic(16, 2, zero, zero + 256),
				(zero + 256, 16, 16),
				"second level digest",
			);
			assert_eq!(
				digest_build_iterator_basic(16, 2, zero, zero + 4096),
				(zero + 4096, 16, 16),
				"!(block % interval^3), but there's only 2 digest levels",
			);
		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn suggest_digest_inclusion_returns_level3_iterator() {
		fn test_with_zero(zero: u64) {
			assert_eq!(
				digest_build_iterator_basic(16, 3, zero, zero + 4096),
				(zero + 4096, 16, 256),
				"third level digest: beginning",
			);
			assert_eq!(
				digest_build_iterator_basic(16, 3, zero, zero + 8192),
				(zero + 8192, 16, 256),
				"third level digest: next",
			);
		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn digest_iterator_returns_level1_blocks() {
		fn test_with_zero(zero: u64) {
			assert_eq!(digest_build_iterator_blocks(16, 1, zero, zero + 16, None),
				[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
					.iter().map(|item| zero + item).collect::<Vec<_>>());
			assert_eq!(digest_build_iterator_blocks(16, 1, zero, zero + 256, None),
				[241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]
					.iter().map(|item| zero + item).collect::<Vec<_>>());
			assert_eq!(digest_build_iterator_blocks(16, 2, zero, zero + 32, None),
				[17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
					.iter().map(|item| zero + item).collect::<Vec<_>>());
			assert_eq!(digest_build_iterator_blocks(16, 3, zero, zero + 4080, None),
				[4065, 4066, 4067, 4068, 4069, 4070, 4071, 4072, 4073, 4074, 4075, 4076, 4077, 4078, 4079]
					.iter().map(|item| zero + item).collect::<Vec<_>>());
		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn digest_iterator_returns_level1_and_level2_blocks() {
		fn test_with_zero(zero: u64) {
			assert_eq!(digest_build_iterator_blocks(16, 2, zero, zero + 256, None),
				[
					// level2 points to previous 16-1 level1 digests:
					16, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 208, 224, 240,
					// level2 is a level1 digest of 16-1 previous blocks:
					241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255,
				].iter().map(|item| zero + item).collect::<Vec<_>>(),
			);
			assert_eq!(digest_build_iterator_blocks(16, 2, zero, zero + 4096, None),
				[
					// level2 points to previous 16-1 level1 digests:
					3856, 3872, 3888, 3904, 3920, 3936, 3952, 3968, 3984, 4000, 4016, 4032, 4048, 4064, 4080,
					// level2 is a level1 digest of 16-1 previous blocks:
					4081, 4082, 4083, 4084, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095,
				].iter().map(|item| zero + item).collect::<Vec<_>>(),
			);
		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn digest_iterator_returns_level1_and_level2_and_level3_blocks() {
		fn test_with_zero(zero: u64) {
			assert_eq!(digest_build_iterator_blocks(16, 3, zero, zero + 4096, None),
				[
					// level3 points to previous 16-1 level2 digests:
					256, 512, 768, 1024, 1280, 1536, 1792, 2048, 2304, 2560, 2816, 3072, 3328, 3584, 3840,
					// level3 points to previous 16-1 level1 digests:
					3856, 3872, 3888, 3904, 3920, 3936, 3952, 3968, 3984, 4000, 4016, 4032, 4048, 4064, 4080,
					// level3 is a level1 digest of 16-1 previous blocks:
					4081, 4082, 4083, 4084, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095,
				].iter().map(|item| zero + item).collect::<Vec<_>>(),
			);
		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn digest_iterator_returns_skewed_digest_blocks() {
		fn test_with_zero(zero: u64) {
			assert_eq!(digest_build_iterator_blocks(16, 3, zero, zero + 4096, Some(zero + 1338)),
				[
					// level3 MUST point to previous 16-1 level2 digests, BUT there are only 5:
					256, 512, 768, 1024, 1280,
					// level3 MUST point to previous 16-1 level1 digests, BUT there are only 3:
					1296, 1312, 1328,
					// level3 MUST be a level1 digest of 16-1 previous blocks, BUT there are only 9:
					1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337,
				].iter().map(|item| zero + item).collect::<Vec<_>>(),
			);
		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}

	#[test]
	fn digest_iterator_returns_skewed_digest_blocks_skipping_level() {
		fn test_with_zero(zero: u64) {
			assert_eq!(digest_build_iterator_blocks(16, 3, zero, zero + 4096, Some(zero + 1284)),
				[
					// level3 MUST point to previous 16-1 level2 digests, BUT there are only 5:
					256, 512, 768, 1024, 1280,
					// level3 MUST point to previous 16-1 level1 digests, BUT there are NO ANY L1-digests:
					// level3 MUST be a level1 digest of 16-1 previous blocks, BUT there are only 3:
					1281, 1282, 1283,
				].iter().map(|item| zero + item).collect::<Vec<_>>(),
			);
		}

		test_with_zero(0);
		test_with_zero(16);
		test_with_zero(17);
	}
}
