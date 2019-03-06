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

//! Structures and functions to return blocks whose changes are to be included
//! in given block' changes trie.

use crate::changes_trie::Configuration;

/// Returns iterator of OTHER blocks that are required for inclusion into
/// changes trie of given block.
pub fn digest_build_iterator(config: &Configuration, block: u64) -> DigestBuildIterator {
	// prepare digest build parameters
	let (_, _, digest_step) = match config.digest_level_at_block(block) {
		Some((current_level, digest_interval, digest_step)) =>
			(current_level, digest_interval, digest_step),
		None => return DigestBuildIterator::empty(),
	};

	DigestBuildIterator::new(block, config.digest_interval, digest_step)
}

/// Changes trie build iterator that returns numbers of OTHER blocks that are
/// required for inclusion into changes trie of given block.
#[derive(Debug)]
pub struct DigestBuildIterator {
	/// Block we're building changes trie for.
	block: u64,
	/// Interval for creation digest blocks.
	digest_interval: u64,
	/// Step of current blocks range.
	current_step: u64,
	/// Current blocks range.
	current_range: Option<::std::iter::StepBy<::std::ops::Range<u64>>>,
	/// Max step of blocks range.
	max_step: u64,
}

impl DigestBuildIterator {
	/// Create new digest build iterator.
	pub fn new(block: u64, digest_interval: u64, max_step: u64) -> Self {
		DigestBuildIterator {
			block, digest_interval, max_step,
			current_step: 0,
			current_range: None,
		}
	}

	/// Create empty digest build iterator.
	pub fn empty() -> Self {
		Self::new(0, 0, 0)
	}
}

impl Iterator for DigestBuildIterator {
	type Item = u64;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(next) = self.current_range.as_mut().and_then(|iter| iter.next()) {
			return Some(next);
		}

		// we are safe to use non-checking mul/sub versions here because:
		// DigestBuildIterator is created only by internal function that is checking
		// that all multiplications/subtractions are safe within max_step limit

		let next_step = if self.current_step == 0 { 1 } else { self.current_step * self.digest_interval };
		if next_step > self.max_step {
			return None;
		}

		self.current_step = next_step;
		self.current_range = Some(
			((self.block - self.current_step * self.digest_interval + self.current_step)..self.block)
				.step_by(self.current_step as usize)
		);

		Some(self.current_range.as_mut()
			.expect("assigned one line above; qed")
			.next()
			.expect("X - I^(N+1) + I^N > X when X,I,N are > 1; qed"))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn digest_build_iterator(digest_interval: u64, digest_levels: u32, block: u64) -> DigestBuildIterator {
		super::digest_build_iterator(&Configuration { digest_interval, digest_levels }, block)
	}

	fn digest_build_iterator_basic(digest_interval: u64, digest_levels: u32, block: u64) -> (u64, u64, u64) {
		let iter = digest_build_iterator(digest_interval, digest_levels, block);
		(iter.block, iter.digest_interval, iter.max_step)
	}

	fn digest_build_iterator_blocks(digest_interval: u64, digest_levels: u32, block: u64) -> Vec<u64> {
		digest_build_iterator(digest_interval, digest_levels, block).collect()
	}

	#[test]
	fn suggest_digest_inclusion_returns_empty_iterator() {
		let empty = (0, 0, 0);
		assert_eq!(digest_build_iterator_basic(4, 16, 0), empty, "block is 0");
		assert_eq!(digest_build_iterator_basic(0, 16, 64), empty, "digest_interval is 0");
		assert_eq!(digest_build_iterator_basic(1, 16, 64), empty, "digest_interval is 1");
		assert_eq!(digest_build_iterator_basic(4, 0, 64), empty, "digest_levels is 0");
		assert_eq!(digest_build_iterator_basic(4, 16, 1), empty, "digest is not required for this block");
		assert_eq!(digest_build_iterator_basic(4, 16, 2), empty, "digest is not required for this block");
		assert_eq!(digest_build_iterator_basic(4, 16, 15), empty, "digest is not required for this block");
		assert_eq!(digest_build_iterator_basic(4, 16, 17), empty, "digest is not required for this block");
		assert_eq!(digest_build_iterator_basic(::std::u64::MAX / 2 + 1, 16, ::std::u64::MAX), empty, "digest_interval * 2 is greater than u64::MAX");
	}

	#[test]
	fn suggest_digest_inclusion_returns_level1_iterator() {
		assert_eq!(digest_build_iterator_basic(16, 1, 16), (16, 16, 1), "!(block % interval) && first digest level == block");
		assert_eq!(digest_build_iterator_basic(16, 1, 256), (256, 16, 1), "!(block % interval^2), but there's only 1 digest level");
		assert_eq!(digest_build_iterator_basic(16, 2, 32), (32, 16, 1), "second level digest is not required for this block");
		assert_eq!(digest_build_iterator_basic(16, 3, 4080), (4080, 16, 1), "second && third level digest are not required for this block");
	}

	#[test]
	fn suggest_digest_inclusion_returns_level2_iterator() {
		assert_eq!(digest_build_iterator_basic(16, 2, 256), (256, 16, 16), "second level digest");
		assert_eq!(digest_build_iterator_basic(16, 2, 4096), (4096, 16, 16), "!(block % interval^3), but there's only 2 digest levels");
	}

	#[test]
	fn suggest_digest_inclusion_returns_level3_iterator() {
		assert_eq!(digest_build_iterator_basic(16, 3, 4096), (4096, 16, 256), "third level digest: beginning");
		assert_eq!(digest_build_iterator_basic(16, 3, 8192), (8192, 16, 256), "third level digest: next");
	}

	#[test]
	fn digest_iterator_returns_level1_blocks() {
		assert_eq!(digest_build_iterator_blocks(16, 1, 16),
			vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
		assert_eq!(digest_build_iterator_blocks(16, 1, 256),
			vec![241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]);
		assert_eq!(digest_build_iterator_blocks(16, 2, 32),
			vec![17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]);
		assert_eq!(digest_build_iterator_blocks(16, 3, 4080),
			vec![4065, 4066, 4067, 4068, 4069, 4070, 4071, 4072, 4073, 4074, 4075, 4076, 4077, 4078, 4079]);
	}

	#[test]
	fn digest_iterator_returns_level1_and_level2_blocks() {
		assert_eq!(digest_build_iterator_blocks(16, 2, 256),
			vec![
				// level2 is a level1 digest of 16-1 previous blocks:
				241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255,
				// level2 points to previous 16-1 level1 digests:
				16, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 208, 224, 240,
			],
		);
		assert_eq!(digest_build_iterator_blocks(16, 2, 4096),
			vec![
				// level2 is a level1 digest of 16-1 previous blocks:
				4081, 4082, 4083, 4084, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095,
				// level2 points to previous 16-1 level1 digests:
				3856, 3872, 3888, 3904, 3920, 3936, 3952, 3968, 3984, 4000, 4016, 4032, 4048, 4064, 4080,
			],
		);
	}

	#[test]
	fn digest_iterator_returns_level1_and_level2_and_level3_blocks() {
		assert_eq!(digest_build_iterator_blocks(16, 3, 4096),
			vec![
				// level3 is a level1 digest of 16-1 previous blocks:
				4081, 4082, 4083, 4084, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095,
				// level3 points to previous 16-1 level1 digests:
				3856, 3872, 3888, 3904, 3920, 3936, 3952, 3968, 3984, 4000, 4016, 4032, 4048, 4064, 4080,
				// level3 points to previous 16-1 level2 digests:
				256, 512, 768, 1024, 1280, 1536, 1792, 2048, 2304, 2560, 2816, 3072, 3328, 3584, 3840,
			],
		);
	}
}
