// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Substrate changes trie configuration.

#[cfg(any(feature = "std", test))]
use serde::{Serialize, Deserialize};
use parity_codec::{Encode, Decode};
use num_traits::Zero;

/// Substrate changes trie configuration.
#[cfg_attr(any(feature = "std", test), derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq, Default, Encode, Decode)]
pub struct ChangesTrieConfiguration {
	/// Interval (in blocks) at which level1-digests are created. Digests are not
	/// created when this is less or equal to 1.
	pub digest_interval: u32,
	/// Maximal number of digest levels in hierarchy. 0 means that digests are not
	/// created at all (even level1 digests). 1 means only level1-digests are created.
	/// 2 means that every digest_interval^2 there will be a level2-digest, and so on.
	/// Please ensure that maximum digest interval (i.e. digest_interval^digest_levels)
	/// is within `u32` limits. Otherwise you'll never see digests covering such intervals
	/// && maximal digests interval will be truncated to the last interval that fits
	/// `u32` limits.
	pub digest_levels: u32,
}

impl ChangesTrieConfiguration {
	/// Is digest build enabled?
	pub fn is_digest_build_enabled(&self) -> bool {
		self.digest_interval > 1 && self.digest_levels > 0
	}

	/// Do we need to build digest at given block?
	pub fn is_digest_build_required_at_block<Number>(&self, block: Number) -> bool
		where
			Number: From<u32> + PartialEq + ::rstd::ops::Rem<Output=Number> + Zero,
	{
		block != 0.into()
			&& self.is_digest_build_enabled()
			&& (block % self.digest_interval.into()).is_zero()
	}

	/// Returns max digest interval. One if digests are not created at all.
	pub fn max_digest_interval(&self) -> u32 {
		if !self.is_digest_build_enabled() {
			return 1;
		}

		// we'll get >1 loop iteration only when bad configuration parameters are selected
		let mut current_level = self.digest_levels;
		loop {
			if let Some(max_digest_interval) = self.digest_interval.checked_pow(current_level) {
				return max_digest_interval;
			}

			current_level = current_level - 1;
		}
	}

	/// Returns Some if digest must be built at given block number.
	/// The tuple is:
	/// (
	///  digest level
	///  digest interval (in blocks)
	///  step between blocks we're interested in when digest is built
	/// )
	pub fn digest_level_at_block<Number>(&self, block: Number) -> Option<(u32, u32, u32)>
		where
			Number: Clone + From<u32> + PartialEq + ::rstd::ops::Rem<Output=Number> + Zero,
	{
		if !self.is_digest_build_required_at_block(block.clone()) {
			return None;
		}

		let mut digest_interval = self.digest_interval;
		let mut current_level = 1u32;
		let mut digest_step = 1u32;
		while current_level < self.digest_levels {
			let new_digest_interval = match digest_interval.checked_mul(self.digest_interval) {
				Some(new_digest_interval) if (block.clone() % new_digest_interval.into()).is_zero()
					=> new_digest_interval,
				_ => break,
			};

			digest_step = digest_interval;
			digest_interval = new_digest_interval;
			current_level = current_level + 1;
		}

		Some((
			current_level,
			digest_interval,
			digest_step,
		))
	}
}

#[cfg(test)]
mod tests {
	use super::ChangesTrieConfiguration;

	fn config(interval: u32, levels: u32) -> ChangesTrieConfiguration {
		ChangesTrieConfiguration {
			digest_interval: interval,
			digest_levels: levels,
		}
	}

	#[test]
	fn is_digest_build_enabled_works() {
		assert!(!config(0, 100).is_digest_build_enabled());
		assert!(!config(1, 100).is_digest_build_enabled());
		assert!(config(2, 100).is_digest_build_enabled());
		assert!(!config(100, 0).is_digest_build_enabled());
		assert!(config(100, 1).is_digest_build_enabled());
	}

	#[test]
	fn is_digest_build_required_at_block_works() {
		assert!(!config(8, 4).is_digest_build_required_at_block(0u64));
		assert!(!config(8, 4).is_digest_build_required_at_block(1u64));
		assert!(!config(8, 4).is_digest_build_required_at_block(2u64));
		assert!(!config(8, 4).is_digest_build_required_at_block(4u64));
		assert!(config(8, 4).is_digest_build_required_at_block(8u64));
		assert!(!config(8, 4).is_digest_build_required_at_block(9u64));
		assert!(config(8, 4).is_digest_build_required_at_block(64u64));
		assert!(config(8, 4).is_digest_build_required_at_block(64u64));
		assert!(config(8, 4).is_digest_build_required_at_block(512u64));
		assert!(config(8, 4).is_digest_build_required_at_block(4096u64));
		assert!(!config(8, 4).is_digest_build_required_at_block(4103u64));
		assert!(config(8, 4).is_digest_build_required_at_block(4104u64));
		assert!(!config(8, 4).is_digest_build_required_at_block(4108u64));
	}

	#[test]
	fn digest_level_at_block_works() {
		assert_eq!(config(8, 4).digest_level_at_block(0u64), None);
		assert_eq!(config(8, 4).digest_level_at_block(7u64), None);
		assert_eq!(config(8, 4).digest_level_at_block(63u64), None);
		assert_eq!(config(8, 4).digest_level_at_block(8u64), Some((1, 8, 1)));
		assert_eq!(config(8, 4).digest_level_at_block(64u64), Some((2, 64, 8)));
		assert_eq!(config(8, 4).digest_level_at_block(512u64), Some((3, 512, 64)));
		assert_eq!(config(8, 4).digest_level_at_block(4096u64), Some((4, 4096, 512)));
		assert_eq!(config(8, 4).digest_level_at_block(4112u64), Some((1, 8, 1)));
	}

	#[test]
	fn max_digest_interval_works() {
		assert_eq!(config(0, 0).max_digest_interval(), 1);
		assert_eq!(config(2, 2).max_digest_interval(), 4);
		assert_eq!(config(8, 4).max_digest_interval(), 4096);
		assert_eq!(config(::std::u32::MAX, 1024).max_digest_interval(), ::std::u32::MAX);
	}
}
