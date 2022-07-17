// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use crate::primitives::{LeafIndex, NodeIndex};
use mmr_lib::helper;

/// MMR nodes & size -related utilities.
pub struct NodesUtils {
	no_of_leaves: LeafIndex,
}

impl NodesUtils {
	/// Create new instance of MMR nodes utilities for given number of leaves.
	pub fn new(no_of_leaves: LeafIndex) -> Self {
		Self { no_of_leaves }
	}

	/// Calculate number of peaks in the MMR.
	pub fn number_of_peaks(&self) -> NodeIndex {
		self.number_of_leaves().count_ones() as NodeIndex
	}

	/// Return the number of leaves in the MMR.
	pub fn number_of_leaves(&self) -> LeafIndex {
		self.no_of_leaves
	}

	/// Calculate the total size of MMR (number of nodes).
	pub fn size(&self) -> NodeIndex {
		2 * self.no_of_leaves - self.number_of_peaks()
	}

	/// Calculate maximal depth of the MMR.
	pub fn depth(&self) -> u32 {
		if self.no_of_leaves == 0 {
			return 0
		}

		64 - self.no_of_leaves.next_power_of_two().leading_zeros()
	}

	/// Calculate `LeafIndex` for the leaf that added `node_index` to the MMR.
	pub fn leaf_index_that_added_node(node_index: NodeIndex) -> LeafIndex {
		let rightmost_leaf_pos = Self::rightmost_leaf_node_index_from_pos(node_index);
		Self::leaf_node_index_to_leaf_index(rightmost_leaf_pos)
	}

	// Translate a _leaf_ `NodeIndex` to its `LeafIndex`.
	fn leaf_node_index_to_leaf_index(pos: NodeIndex) -> LeafIndex {
		if pos == 0 {
			return 0
		}
		let peaks = helper::get_peaks(pos);
		(pos + peaks.len() as u64) >> 1
	}

	// Starting from any node position get position of rightmost leaf; this is the leaf
	// responsible for the addition of node `pos`.
	fn rightmost_leaf_node_index_from_pos(pos: NodeIndex) -> NodeIndex {
		pos - (helper::pos_height_in_tree(pos) as u64)
	}

	/// Starting from any leaf index, get the sequence of positions of the nodes added
	/// to the mmr when this leaf was added (inclusive of the leaf's position itself).
	/// That is, all of these nodes are right children of their respective parents.
	pub fn right_branch_ending_in_leaf(leaf_index: LeafIndex) -> crate::Vec<NodeIndex> {
		let pos = helper::leaf_index_to_pos(leaf_index);
		let num_parents = leaf_index.trailing_ones() as u64;
		return (pos..=pos + num_parents).collect()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use mmr_lib::helper::leaf_index_to_pos;

	#[test]
	fn should_calculate_node_index_from_leaf_index() {
		for index in 0..100000 {
			let pos = leaf_index_to_pos(index);
			assert_eq!(NodesUtils::leaf_node_index_to_leaf_index(pos), index);
		}
	}

	#[test]
	fn should_calculate_right_branch_correctly() {
		fn left_jump_sequence(leaf_index: LeafIndex) -> Vec<u64> {
			let pos = leaf_index_to_pos(leaf_index);
			let mut right_branch_ending_in_leaf = vec![pos];
			let mut next_pos = pos + 1;
			while mmr_lib::helper::pos_height_in_tree(next_pos) > 0 {
				right_branch_ending_in_leaf.push(next_pos);
				next_pos += 1;
			}
			right_branch_ending_in_leaf
		}

		for leaf_index in 0..100000 {
			let pos = mmr_lib::helper::leaf_index_to_pos(leaf_index);
			assert_eq!(NodesUtils::right_branch_ending_in_leaf(pos), left_jump_sequence(pos));
		}
	}

	#[test]
	fn should_calculate_rightmost_leaf_node_index_from_pos() {
		for pos in 0..100000 {
			let leaf_pos = NodesUtils::rightmost_leaf_node_index_from_pos(pos);
			let leaf_index = NodesUtils::leaf_node_index_to_leaf_index(leaf_pos);
			assert!(NodesUtils::right_branch_ending_in_leaf(leaf_index).contains(&pos));
		}
	}

	#[test]
	fn should_calculate_number_of_leaves_correctly() {
		assert_eq!(
			vec![0, 1, 2, 3, 4, 9, 15, 21]
				.into_iter()
				.map(|n| NodesUtils::new(n).depth())
				.collect::<Vec<_>>(),
			vec![0, 1, 2, 3, 3, 5, 5, 6]
		);
	}

	#[test]
	fn should_calculate_depth_correclty() {
		assert_eq!(
			vec![0, 1, 2, 3, 4, 9, 15, 21]
				.into_iter()
				.map(|n| NodesUtils::new(n).number_of_leaves())
				.collect::<Vec<_>>(),
			vec![0, 1, 2, 3, 4, 9, 15, 21]
		);
	}

	#[test]
	fn should_calculate_number_of_peaks_correctly() {
		assert_eq!(
			vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 21]
				.into_iter()
				.map(|n| NodesUtils::new(n).number_of_peaks())
				.collect::<Vec<_>>(),
			vec![0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 3]
		);
	}

	#[test]
	fn should_calculate_the_size_correctly() {
		let _ = env_logger::try_init();

		let leaves = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 21];
		let sizes = vec![0, 1, 3, 4, 7, 8, 10, 11, 15, 16, 18, 19, 22, 23, 25, 26, 39];
		assert_eq!(
			leaves
				.clone()
				.into_iter()
				.map(|n| NodesUtils::new(n).size())
				.collect::<Vec<_>>(),
			sizes.clone()
		);

		// size cross-check
		let mut actual_sizes = vec![];
		for s in &leaves[1..] {
			crate::tests::new_test_ext().execute_with(|| {
				let mut mmr = crate::mmr::Mmr::<
					crate::mmr::storage::RuntimeStorage,
					crate::mock::Test,
					_,
					_,
				>::new(0);
				for i in 0..*s {
					mmr.push(i);
				}
				actual_sizes.push(mmr.size());
			})
		}
		assert_eq!(sizes[1..], actual_sizes[..]);
	}
}
