// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Merkle Mountain Range utilities.


/// MMR nodes utilities.
pub struct NodesUtils {
	size: u64,
}

impl NodesUtils {
	/// Create new instance of MMR nodes utilities.
	pub fn new(size: u64) -> Self {
		Self { size }
	}

	/// Return number of peaks in the MMR.
	pub fn number_of_peaks(&self) -> u64 {
		self.number_of_leaves().count_ones() as u64
	}

	/// Return the number of leaves in the MMR.
	pub fn number_of_leaves(&self) -> u64 {
		if self.size == 0 {
			return 0;
		}
		(self.size / 2).next_power_of_two()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_calculate_number_of_leaves_correctly() {
		assert_eq!(
			vec![0, 1, 2, 3, 4, 9, 15, 21]
				.into_iter()
				.map(|n| NodesUtils::new(n).number_of_leaves())
				.collect::<Vec<_>>(),
			vec![0, 1, 2, 2, 3, 6, 8, 12]
		);
	}


	#[test]
	fn should_calculate_number_of_peaks_correctly() {
		assert_eq!(
			vec![0, 1, 2, 3, 4, 9, 15, 21]
				.into_iter()
				.map(|n| NodesUtils::new(n).number_of_peaks())
				.collect::<Vec<_>>(),
			vec![0, 1, 1, 2, 2, 2, 1, 2]
		);
	}
}
