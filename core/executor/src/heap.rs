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

//! This module implements a buddy allocation heap.
//! It uses a binary tree and follows the concepts outlined in
//! https://en.wikipedia.org/wiki/Buddy_memory_allocation.

extern crate fnv;

use std::vec;
use log::trace;
use self::fnv::FnvHashMap;

// The pointers need to be aligned to 8 bytes.
const ALIGNMENT: u32 = 8;

// The block size needs to be a multiple of the memory alignment
// requirement. This is so that the pointer returned by `allocate()`
// always fulfills the alignment. In buddy allocation a pointer always
// points to the start of a block, which with a fitting block size
// will then be a multiple of the alignment requirement.
const BLOCK_SIZE: u32 = 8192; // 2^13 bytes

#[allow(path_statements)]
fn _assert_block_size_aligned() {
	// mem::transmute checks that type sizes are equal.
	// this enables us to assert that pointers are aligned -- at compile time.
	::std::mem::transmute::<[u8; BLOCK_SIZE as usize % ALIGNMENT as usize], [u8; 0]>;
}

#[derive(PartialEq, Copy, Clone)]
enum Node {
	Free,
	Full,
	Split,
}

/// A buddy allocation heap, which tracks allocations and deallocations
/// using a binary tree.
pub struct Heap {
	allocated_bytes: FnvHashMap<u32, u32>,
	levels: u32,
	ptr_offset: u32,
	tree: vec::Vec<Node>,
	total_size: u32,
}

impl Heap {

	/// Creates a new buddy allocation heap.
	///
	/// # Arguments
	///
	/// * `ptr_offset` - The pointers returned by `allocate()`
	///   start from this offset on. The pointer offset needs
	///   to be aligned to a multiple of 8, hence a padding might
	///   be added to align `ptr_offset` properly.
	///
	/// * `heap_size` - The size available to this heap instance
	///   (in bytes) for allocating memory.
	///
	pub fn new(mut ptr_offset: u32, heap_size: u32) -> Self {
		let padding = ptr_offset % ALIGNMENT;
		if padding != 0 {
			ptr_offset += ALIGNMENT - padding;
		}

		let leaves = heap_size / BLOCK_SIZE;
		let levels = Heap::get_necessary_tree_levels(leaves);
		let node_count: usize = (1 << levels + 1) - 1;

		Heap {
			allocated_bytes: FnvHashMap::default(),
			levels,
			ptr_offset,
			tree: vec![Node::Free; node_count],
			total_size: 0,
		}
	}

	/// Gets requested number of bytes to allocate and returns a pointer.
	pub fn allocate(&mut self, size: u32) -> u32 {
		// Get the requested level from number of blocks requested
		let blocks_needed = (size + BLOCK_SIZE - 1) / BLOCK_SIZE;
		let block_offset = match self.allocate_block_in_tree(blocks_needed) {
			Some(v) => v,
			None => return 0,
		};

		let ptr = BLOCK_SIZE * block_offset as u32;
		self.allocated_bytes.insert(ptr, size as u32);

		self.total_size += size;
		trace!(target: "wasm-heap", "Heap size over {} bytes after allocation", self.total_size);

		self.ptr_offset + ptr
	}

	fn allocate_block_in_tree(&mut self, blocks_needed: u32) -> Option<usize> {
		let levels_needed = Heap::get_necessary_tree_levels(blocks_needed);
		if levels_needed > self.levels {
			trace!(target: "wasm-heap", "Heap is too small: {:?} > {:?}", levels_needed, self.levels);
			return None;
		}

		// Start at tree root and traverse down
		let mut index = 0;
		let mut current_level = self.levels;
		'down: loop {
			let buddy_exists = index & 1 == 1;

			if current_level == levels_needed {
				if self.tree[index] == Node::Free {
					self.tree[index] = Node::Full;

					if index > 0 {
						let parent = self.get_parent_node_index(index);
						self.update_parent_nodes(parent);
					}

					break 'down;
				}
			} else {
				match self.tree[index] {
					Node::Full => {
						if buddy_exists {
							// Check if buddy is free
							index += 1;
						} else {
							break 'down;
						}
						continue 'down;
					},

					Node::Free => {
						// If node is free we split it and descend further down
						self.tree[index] = Node::Split;
						index = index * 2 + 1;
						current_level -= 1;
						continue 'down;
					},

					Node::Split => {
						// Descend further
						index = index * 2 + 1;
						current_level -= 1;
						continue 'down;
					},
				}
			}

			if buddy_exists {
				// If a buddy exists it needs to be checked as well
				index += 1;
				continue 'down;
			}

			// Backtrack once we're at the bottom and haven't matched a free block yet
			'up: loop {
				if index == 0 {
					trace!(target: "wasm-heap", "Heap is too small: tree root reached.");
					return None;
				}

				index = self.get_parent_node_index(index);
				current_level += 1;
				let has_buddy = index & 1 == 1;
				if has_buddy {
					index += 1;
					break 'up;
				}
			}
		}

		let current_level_offset = (1 << self.levels - current_level) - 1;
		let level_offset = index - current_level_offset;

		let block_offset = level_offset * (1 << current_level);
		Some(block_offset as usize)
	}

	/// Deallocates all blocks which were allocated for a pointer.
	pub fn deallocate(&mut self, mut ptr: u32) {
		ptr -= self.ptr_offset;

		let allocated_size = match self.allocated_bytes.get(&ptr) {
			Some(v) => *v,

			// If nothing has been allocated for the pointer nothing happens
			None => return (),
		};

		let count_blocks = (allocated_size + BLOCK_SIZE - 1) / BLOCK_SIZE;
		let block_offset = ptr / BLOCK_SIZE;
		self.free(block_offset, count_blocks);
		self.allocated_bytes.remove(&ptr).unwrap_or_default();

		self.total_size = self.total_size.checked_sub(allocated_size).unwrap_or(0);
		trace!(target: "wasm-heap", "Heap size over {} bytes after deallocation", self.total_size);
	}

	fn free(&mut self, block_offset: u32, count_blocks: u32) {
		let requested_level = Heap::get_necessary_tree_levels(count_blocks);
		let current_level_offset = (1 << self.levels - requested_level) - 1;
		let level_offset = block_offset / (1 << requested_level);
		let index_offset = current_level_offset + level_offset;

		if index_offset > self.tree.len() as u32 - 1 {
			trace!(target: "wasm-heap", "Index offset {} is > length of tree {}", index_offset, self.tree.len());
		}

		self.free_and_merge(index_offset as usize);

		let parent = self.get_parent_node_index(index_offset as usize);
		self.update_parent_nodes(parent);
	}

	fn get_parent_node_index(&mut self, index: usize) -> usize {
		(index + 1) / 2 - 1
	}

	fn free_and_merge(&mut self, index: usize) {
		self.tree[index] = Node::Free;

		if index == 0 {
			return;
		}

		let has_right_buddy = (index & 1) == 1;
		let other_node = if has_right_buddy {
			index + 1
		} else {
			index - 1
		};

		if self.tree[other_node] == Node::Free {
			let parent = self.get_parent_node_index(index);
			self.free_and_merge(parent);
		}
	}

	fn update_parent_nodes(&mut self, index: usize) {
		let left_child = index * 2 + 1;
		let right_child = index * 2 + 2;

		let children_free = self.tree[left_child] == Node::Free && self.tree[right_child] == Node::Free;
		let children_full = self.tree[left_child] == Node::Full && self.tree[right_child] == Node::Full;
		if children_free {
			self.tree[index] = Node::Free;
		} else if children_full {
			self.tree[index] = Node::Full;
		} else {
			self.tree[index] = Node::Split;
		}

		if index == 0 {
			// Tree root
			return;
		}

		let parent = self.get_parent_node_index(index);
		self.update_parent_nodes(parent);
	}

	fn get_necessary_tree_levels(count_blocks: u32) -> u32 {
		if count_blocks == 0 {
			0
		} else {
			let mut necessary_levels = 0;
			let mut necessary_blocks = count_blocks.next_power_of_two();
			while {necessary_blocks >>= 1; necessary_blocks > 0} {
				necessary_levels += 1;
			}
			necessary_levels
		}
	}

}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_always_align_pointers_to_multiples_of_8() {
		let heap_size = BLOCK_SIZE * 4;
		let mut heap = super::Heap::new(13, heap_size);

		let ptr = heap.allocate(1);
		assert_eq!(ptr, 16); // 16 is the next multiple of 8 from 13
	}

	#[test]
	fn should_start_first_pointer_at_offset() {
		let start_offset = 40;
		let heap_size = BLOCK_SIZE * 4;
		let mut heap = super::Heap::new(start_offset, heap_size);

		let ptr = heap.allocate(BLOCK_SIZE - 1);
		assert_eq!(ptr, start_offset);
	}

	#[test]
	fn should_start_second_pointer_at_second_block() {
		let start_offset = 40;
		let heap_size = BLOCK_SIZE * 4;
		let mut heap = super::Heap::new(start_offset, heap_size);

		let _ptr1 = heap.allocate(BLOCK_SIZE - 1);
		let ptr2 = heap.allocate(BLOCK_SIZE - 1);
		assert_eq!(ptr2, start_offset + BLOCK_SIZE);
	}

	#[test]
	fn should_not_panic_on_deallocation_of_nonexistent_pointer() {
		let heap_size = BLOCK_SIZE * 4;
		let mut heap = super::Heap::new(1, heap_size);
		let ret = heap.deallocate(heap_size + 1);
		assert_eq!(ret, ());
	}

	#[test]
	fn should_calculate_tree_size_from_heap_size() {
		let heap_size = BLOCK_SIZE * 4;
		let heap = super::Heap::new(1, heap_size);

		assert_eq!(heap.levels, 2);
	}

	#[test]
	fn should_round_tree_size_to_nearest_possible() {
		let heap_size = BLOCK_SIZE * 4 + 1;
		let heap = super::Heap::new(1, heap_size);

		assert_eq!(heap.levels, 2);
	}

	#[test]
	fn heap_size_should_stay_zero_in_total() {
		let heap_size = BLOCK_SIZE * 4;
		let mut heap = super::Heap::new(1, heap_size);
		assert_eq!(heap.total_size, 0);

		let ptr = heap.allocate(42);
		assert_eq!(heap.total_size, 42);

		heap.deallocate(ptr);
		assert_eq!(heap.total_size, 0);
	}

	#[test]
	fn heap_size_should_stay_constant() {
		let heap_size = BLOCK_SIZE * 4;
		let mut heap = super::Heap::new(9, heap_size);
		for _ in 1..10 {
			assert_eq!(heap.total_size, 0);

			let ptr = heap.allocate(42);
			assert_eq!(ptr, 16);
			assert_eq!(heap.total_size, 42);

			heap.deallocate(ptr);
			assert_eq!(heap.total_size, 0);
		}

		assert_eq!(heap.total_size, 0);
	}

	#[test]
	fn should_allocate_exactly_entire_tree() {
		let blocks = 16;
		let heap_size = BLOCK_SIZE * blocks;
		let mut heap = super::Heap::new(0, heap_size);

		for i in 0..16 {
			let ptr = heap.allocate(BLOCK_SIZE);
			assert_eq!(ptr, i * BLOCK_SIZE);
			assert_eq!(heap.total_size, (i+1) * BLOCK_SIZE);
		}

		let ptr = heap.allocate(BLOCK_SIZE);
		assert_eq!(ptr, 0);
	}

	#[test]
	fn should_deallocate_entire_tree_exactly() {
		let blocks = 12;
		let heap_size = BLOCK_SIZE * blocks;
		let mut heap = super::Heap::new(0, heap_size);
		for i in 0..blocks {
			let ptr = heap.allocate(BLOCK_SIZE);
			assert_eq!(ptr, i * BLOCK_SIZE);
			assert_eq!(heap.total_size, (i+1) * BLOCK_SIZE);
		}

		for i in 0..blocks {
			let ptr = i * BLOCK_SIZE;
			heap.deallocate(ptr);
			assert_eq!(heap.total_size, blocks * BLOCK_SIZE - (i+1) * BLOCK_SIZE);
		}

		assert_eq!(heap.total_size, 0);
	}

	#[test]
	fn should_allocate_pointers_with_odd_blocks_properly() {
		let blocks = 6;
		let heap_size = BLOCK_SIZE * blocks;
		let mut heap = super::Heap::new(0, heap_size);

		let ptr = heap.allocate(3 * BLOCK_SIZE);
		assert_eq!(ptr, 0);

		let ptr = heap.allocate(BLOCK_SIZE);
		assert_eq!(ptr, 4 * BLOCK_SIZE);
	}

	#[test]
	fn should_handle_odd_blocks_properly() {
		let blocks = 8;
		let heap_size = BLOCK_SIZE * blocks;
		let mut heap = super::Heap::new(0, heap_size);

		let ptr = heap.allocate(3 * BLOCK_SIZE);
		assert_eq!(ptr, 0);

		let ptr = heap.allocate(3 * BLOCK_SIZE);
		assert_eq!(ptr, 4 * BLOCK_SIZE);
	}

	#[test]
	fn should_calculate_zero_tree_levels_for_zero_blocks() {
		let count_blocks = 0;
		let levels = Heap::get_necessary_tree_levels(count_blocks);
		assert_eq!(levels, 0);
	}

	#[test]
	fn should_calculate_necessary_tree_levels_correctly() {
		let count_blocks = 1;
		let levels = Heap::get_necessary_tree_levels(count_blocks);
		assert_eq!(levels, 0);

		let count_blocks = 2;
		let levels = Heap::get_necessary_tree_levels(count_blocks);
		assert_eq!(levels, 1);

		let count_blocks = 3;
		let levels = Heap::get_necessary_tree_levels(count_blocks);
		assert_eq!(levels, 2);

		let count_blocks = 4;
		let levels = Heap::get_necessary_tree_levels(count_blocks);
		assert_eq!(levels, 2);

		let count_blocks = 5;
		let levels = Heap::get_necessary_tree_levels(count_blocks);
		assert_eq!(levels, 3);
	}

}
