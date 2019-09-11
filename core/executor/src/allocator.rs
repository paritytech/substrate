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

//! This module implements a freeing-bump allocator.
//!
//! The algorithm is as follows:
//! We store `N` linked list heads, where `N` is the total number of sizes
//! of allocations to support. A simple set is powers of two from 8 bytes
//! to 16,777,216 bytes (2^3 - 2^24 inclusive), resulting in `N = 22`:
//!
//! ```ignore
//!	let mut heads [u64; N] = [0; N];
//! fn size(n: u64) -> u64 { 8 << n }
//! let mut bumper = 0;
//! fn bump(n: u64) -> u64 { let res = bumper; bumper += n; res }
//! ```
//!
//! We assume there is a slab of heap to be allocated:
//!
//! ```ignore
//! let mut heap = [0u8; HEAP_SIZE];
//! ```
//!
//! Whenever we allocate, we select the lowest linked list item size that
//! will fit the allocation (i.e. the next highest power of two).
//! We then check to see if the linked list is empty. If empty, we use
//! the bump allocator to get the allocation with an extra 8 bytes
//! preceding it. We initialise those preceding 8 bytes to identify the
//! list to which it belongs (e.g. `0x__ffffffffffffff` where `__` is the
//! linked list index). If it is not empty, we unlink the first item from
//! the linked list and then reset the 8 preceding bytes so they now record
//! the identity of the linked list.
//!
//! To deallocate we use the preceding 8 bytes of the allocation to knit
//! back the allocation into the linked list from the head.

use crate::error::{Error, Result};
use log::trace;
use wasmi::{MemoryRef, memory_units::Bytes};
use wasm_interface::{Pointer, WordSize};

// The pointers need to be aligned to 8 bytes. This is because the
// maximum value type handled by wasm32 is u64.
const ALIGNMENT: u32 = 8;

// The pointer returned by `allocate()` needs to fulfill the alignment
// requirement. In our case a pointer will always be a multiple of
// 8, as long as the first pointer is aligned to 8 bytes.
// This is because all pointers will contain a 8 byte prefix (the list
// index) and then a subsequent item of 2^x bytes, where x = [3..24].
const N: usize = 22;
const MAX_POSSIBLE_ALLOCATION: u32 = 16777216; // 2^24 bytes
const MIN_POSSIBLE_ALLOCATION: u32 = 8;

// Each pointer is prefixed with 8 bytes, which identify the list index
// to which it belongs.
const PREFIX_SIZE: u32 = 8;

pub struct FreeingBumpHeapAllocator {
	bumper: u32,
	heads: [u32; N],
	heap: MemoryRef,
	max_heap_size: u32,
	ptr_offset: u32,
	total_size: u32,
}

/// Create an allocator error.
fn error(msg: &'static str) -> Error {
	Error::Allocator(msg)
}

impl FreeingBumpHeapAllocator {
	/// Creates a new allocation heap which follows a freeing-bump strategy.
	/// The maximum size which can be allocated at once is 16 MiB.
	///
	/// # Arguments
	///
	/// - `mem` - reference to the linear memory instance on which this allocator operates.
	/// - `heap_base` - the offset from the beginning of the linear memory where the heap starts.
	pub fn new(mem: MemoryRef, heap_base: u32) -> Self {
		let current_size: Bytes = mem.current_size().into();
		let current_size = current_size.0 as u32;

		let mut ptr_offset = heap_base;
		let padding = ptr_offset % ALIGNMENT;
		if padding != 0 {
			ptr_offset += ALIGNMENT - padding;
		}

		let heap_size = current_size - ptr_offset;

		FreeingBumpHeapAllocator {
			bumper: 0,
			heads: [0; N],
			heap: mem,
			max_heap_size: heap_size,
			ptr_offset: ptr_offset,
			total_size: 0,
		}
	}

	/// Gets requested number of bytes to allocate and returns a pointer.
	/// The maximum size which can be allocated at once is 16 MiB.
	/// There is no minimum size, but whatever size is passed into
	/// this function is rounded to the next power of two. If the requested
	/// size is below 8 bytes it will be rounded up to 8 bytes.
	pub fn allocate(&mut self, size: WordSize) -> Result<Pointer<u8>> {
		if size > MAX_POSSIBLE_ALLOCATION {
			return Err(Error::RequestedAllocationTooLarge);
		}

		let size = size.max(MIN_POSSIBLE_ALLOCATION);
		let item_size = size.next_power_of_two();
		if item_size + PREFIX_SIZE + self.total_size > self.max_heap_size {
			return Err(Error::AllocatorOutOfSpace);
		}

		let list_index = (item_size.trailing_zeros() - 3) as usize;
		let ptr: u32 = if self.heads[list_index] != 0 {
			// Something from the free list
			let item = self.heads[list_index];
			let ptr = item + PREFIX_SIZE;
			assert!(
				ptr + item_size <= self.max_heap_size,
				"Pointer is looked up in list of free entries, into which
				only valid values are inserted; qed"
			);

			let four_bytes = self.get_heap_4bytes(item)?;
			self.heads[list_index] = Self::le_bytes_to_u32(four_bytes);
			ptr
		} else {
			// Nothing to be freed. Bump.
			self.bump(item_size)? + PREFIX_SIZE
		};

		// Reset prefix
		(1..PREFIX_SIZE).try_for_each(|i| self.set_heap(ptr - i, 255))?;

		self.set_heap(ptr - PREFIX_SIZE, list_index as u8)?;

		self.total_size = self.total_size + item_size + PREFIX_SIZE;
		trace!(target: "wasm-heap", "Heap size is {} bytes after allocation", self.total_size);

		Ok(Pointer::new(self.ptr_offset + ptr))
	}

	/// Deallocates the space which was allocated for a pointer.
	pub fn deallocate(&mut self, ptr: Pointer<u8>) -> Result<()> {
		let ptr = u32::from(ptr) - self.ptr_offset;
		if ptr < PREFIX_SIZE {
			return Err(error("Invalid pointer for deallocation"));
		}

		let list_index = usize::from(self.get_heap_byte(ptr - PREFIX_SIZE)?);
		(1..PREFIX_SIZE).try_for_each(|i|
			self.get_heap_byte(ptr - i).map(|byte| assert!(byte == 255))
		)?;
		let tail = self.heads[list_index];
		self.heads[list_index] = ptr - PREFIX_SIZE;

		let mut slice = self.get_heap_4bytes(ptr - PREFIX_SIZE)?;
		Self::write_u32_into_le_bytes(tail, &mut slice);
		self.set_heap_4bytes(ptr - PREFIX_SIZE, slice)?;

		let item_size = Self::get_item_size_from_index(list_index);
		self.total_size = self.total_size.checked_sub(item_size as u32 + PREFIX_SIZE)
			.ok_or_else(|| error("Unable to subtract from total heap size without overflow"))?;
		trace!(target: "wasm-heap", "Heap size is {} bytes after deallocation", self.total_size);

		Ok(())
	}

	/// Increases the `bumper` by `item_size + PREFIX_SIZE`.
	///
	/// Returns the `bumper` from before the increase.
	/// Returns an `Error::AllocatorOutOfSpace` if the operation
	/// would exhaust the heap.
	fn bump(&mut self, item_size: u32) -> Result<u32> {
		if self.bumper + PREFIX_SIZE + item_size > self.max_heap_size {
			return Err(Error::AllocatorOutOfSpace);
		}

		let res = self.bumper;
		self.bumper += item_size + PREFIX_SIZE;
		Ok(res)
	}

	fn le_bytes_to_u32(arr: [u8; 4]) -> u32 {
		u32::from_le_bytes(arr)
	}

	fn write_u32_into_le_bytes(bytes: u32, slice: &mut [u8]) {
		slice[..4].copy_from_slice(&bytes.to_le_bytes());
	}

	fn get_item_size_from_index(index: usize) -> usize {
		// we shift 1 by three places, since the first possible item size is 8
		1 << 3 << index
	}

	fn get_heap_4bytes(&mut self, ptr: u32) -> Result<[u8; 4]> {
		let mut arr = [0u8; 4];
		self.heap.get_into(self.ptr_offset + ptr, &mut arr)?;
		Ok(arr)
	}

	fn get_heap_byte(&mut self, ptr: u32) -> Result<u8> {
		let mut arr = [0u8; 1];
		self.heap.get_into(self.ptr_offset + ptr, &mut arr)?;
		Ok(arr[0])
	}

	fn set_heap(&mut self, ptr: u32, value: u8) -> Result<()> {
		self.heap.set(self.ptr_offset + ptr, &[value]).map_err(Into::into)
	}

	fn set_heap_4bytes(&mut self, ptr: u32, value: [u8; 4]) -> Result<()> {
		self.heap.set(self.ptr_offset + ptr, &value).map_err(Into::into)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use wasmi::MemoryInstance;
	use wasmi::memory_units::*;

	const PAGE_SIZE: u32 = 65536;

	/// Makes a pointer out of the given address.
	fn to_pointer(address: u32) -> Pointer<u8> {
		Pointer::new(address)
	}

	#[test]
	fn should_allocate_properly() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), None).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 0);

		// when
		let ptr = heap.allocate(1).unwrap();

		// then
		// returned pointer must start right after `PREFIX_SIZE`
		assert_eq!(ptr, to_pointer(PREFIX_SIZE));
	}

	#[test]
	fn should_always_align_pointers_to_multiples_of_8() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), None).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 13);

		// when
		let ptr = heap.allocate(1).unwrap();

		// then
		// the pointer must start at the next multiple of 8 from 13
		// + the prefix of 8 bytes.
		assert_eq!(ptr, to_pointer(24));
	}

	#[test]
	fn should_increment_pointers_properly() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), None).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 0);

		// when
		let ptr1 = heap.allocate(1).unwrap();
		let ptr2 = heap.allocate(9).unwrap();
		let ptr3 = heap.allocate(1).unwrap();

		// then
		// a prefix of 8 bytes is prepended to each pointer
		assert_eq!(ptr1, to_pointer(PREFIX_SIZE));

		// the prefix of 8 bytes + the content of ptr1 padded to the lowest possible
		// item size of 8 bytes + the prefix of ptr1
		assert_eq!(ptr2, to_pointer(24));

		// ptr2 + its content of 16 bytes + the prefix of 8 bytes
		assert_eq!(ptr3, to_pointer(24 + 16 + PREFIX_SIZE));
	}

	#[test]
	fn should_free_properly() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), None).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 0);
		let ptr1 = heap.allocate(1).unwrap();
		// the prefix of 8 bytes is prepended to the pointer
		assert_eq!(ptr1, to_pointer(PREFIX_SIZE));

		let ptr2 = heap.allocate(1).unwrap();
		// the prefix of 8 bytes + the content of ptr 1 is prepended to the pointer
		assert_eq!(ptr2, to_pointer(24));

		// when
		heap.deallocate(ptr2).unwrap();

		// then
		// then the heads table should contain a pointer to the
		// prefix of ptr2 in the leftmost entry
		assert_eq!(heap.heads[0], u32::from(ptr2) - PREFIX_SIZE);
	}

	#[test]
	fn should_deallocate_and_reallocate_properly() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), None).unwrap();
		let padded_offset = 16;
		let mut heap = FreeingBumpHeapAllocator::new(mem, 13);

		let ptr1 = heap.allocate(1).unwrap();
		// the prefix of 8 bytes is prepended to the pointer
		assert_eq!(ptr1, to_pointer(padded_offset + PREFIX_SIZE));

		let ptr2 = heap.allocate(9).unwrap();
		// the padded_offset + the previously allocated ptr (8 bytes prefix +
		// 8 bytes content) + the prefix of 8 bytes which is prepended to the
		// current pointer
		assert_eq!(ptr2, to_pointer(padded_offset + 16 + PREFIX_SIZE));

		// when
		heap.deallocate(ptr2).unwrap();
		let ptr3 = heap.allocate(9).unwrap();

		// then
		// should have re-allocated
		assert_eq!(ptr3, to_pointer(padded_offset + 16 + PREFIX_SIZE));
		assert_eq!(heap.heads, [0; N]);
	}

	#[test]
	fn should_build_linked_list_of_free_areas_properly() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), None).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 0);

		let ptr1 = heap.allocate(8).unwrap();
		let ptr2 = heap.allocate(8).unwrap();
		let ptr3 = heap.allocate(8).unwrap();

		// when
		heap.deallocate(ptr1).unwrap();
		heap.deallocate(ptr2).unwrap();
		heap.deallocate(ptr3).unwrap();

		// then
		assert_eq!(heap.heads[0], u32::from(ptr3) - PREFIX_SIZE);

		let ptr4 = heap.allocate(8).unwrap();
		assert_eq!(ptr4, ptr3);

		assert_eq!(heap.heads[0], u32::from(ptr2) - PREFIX_SIZE);
	}

	#[test]
	fn should_not_allocate_if_too_large() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), Some(Pages(1))).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 13);

		// when
		let ptr = heap.allocate(PAGE_SIZE - 13);

		// then
		match ptr.unwrap_err() {
			Error::AllocatorOutOfSpace => {},
			e => panic!("Expected allocator out of space error, got: {:?}", e),
		}
	}

	#[test]
	fn should_not_allocate_if_full() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), Some(Pages(1))).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 0);
		let ptr1 = heap.allocate((PAGE_SIZE / 2) - PREFIX_SIZE).unwrap();
		assert_eq!(ptr1, to_pointer(PREFIX_SIZE));

		// when
		let ptr2 = heap.allocate(PAGE_SIZE / 2);

		// then
		// there is no room for another half page incl. its 8 byte prefix
		match ptr2.unwrap_err() {
			Error::AllocatorOutOfSpace => {},
			e => panic!("Expected allocator out of space error, got: {:?}", e),
		}
	}

	#[test]
	fn should_allocate_max_possible_allocation_size() {
		// given
		let pages_needed = (MAX_POSSIBLE_ALLOCATION as usize / PAGE_SIZE as usize) + 1;
		let mem = MemoryInstance::alloc(Pages(pages_needed), Some(Pages(pages_needed))).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 0);

		// when
		let ptr = heap.allocate(MAX_POSSIBLE_ALLOCATION).unwrap();

		// then
		assert_eq!(ptr, to_pointer(PREFIX_SIZE));
	}

	#[test]
	fn should_not_allocate_if_requested_size_too_large() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), None).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 0);

		// when
		let ptr = heap.allocate(MAX_POSSIBLE_ALLOCATION + 1);

		// then
		match ptr.unwrap_err() {
			Error::RequestedAllocationTooLarge => {},
			e => panic!("Expected allocation size too large error, got: {:?}", e),
		}
	}

	#[test]
	fn should_return_error_when_bumper_greater_than_heap_size() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), None).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 0);
		heap.max_heap_size = 64;

		let ptr1 = heap.allocate(32).unwrap();
		assert_eq!(ptr1, to_pointer(PREFIX_SIZE));
		heap.deallocate(ptr1).expect("failed freeing ptr1");
		assert_eq!(heap.total_size, 0);
		assert_eq!(heap.bumper, 40);

		let ptr2 = heap.allocate(16).unwrap();
		assert_eq!(ptr2, to_pointer(48));
		heap.deallocate(ptr2).expect("failed freeing ptr2");
		assert_eq!(heap.total_size, 0);
		assert_eq!(heap.bumper, 64);

		// when
		// the `bumper` value is equal to `max_heap_size` here and any
		// further allocation which would increment the bumper must fail.
		// we try to allocate 8 bytes here, which will increment the
		// bumper since no 8 byte item has been allocated+freed before.
		let ptr = heap.allocate(8);

		// then
		match ptr.unwrap_err() {
			Error::AllocatorOutOfSpace => {},
			e => panic!("Expected allocator out of space error, got: {:?}", e),
		}
	}

	#[test]
	fn should_include_prefixes_in_total_heap_size() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), None).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 1);

		// when
		// an item size of 16 must be used then
		heap.allocate(9).unwrap();

		// then
		assert_eq!(heap.total_size, PREFIX_SIZE + 16);
	}

	#[test]
	fn should_calculate_total_heap_size_to_zero() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), None).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 13);

		// when
		let ptr = heap.allocate(42).unwrap();
		assert_eq!(ptr, to_pointer(16 + PREFIX_SIZE));
		heap.deallocate(ptr).unwrap();

		// then
		assert_eq!(heap.total_size, 0);
	}

	#[test]
	fn should_calculate_total_size_of_zero() {
		// given
		let mem = MemoryInstance::alloc(Pages(1), None).unwrap();
		let mut heap = FreeingBumpHeapAllocator::new(mem, 19);

		// when
		for _ in 1..10 {
			let ptr = heap.allocate(42).unwrap();
			heap.deallocate(ptr).unwrap();
		}

		// then
		assert_eq!(heap.total_size, 0);
	}

	#[test]
	fn should_write_u32_correctly_into_le() {
		// given
		let mut heap = vec![0; 5];

		// when
		FreeingBumpHeapAllocator::write_u32_into_le_bytes(1, &mut heap[0..4]);

		// then
		assert_eq!(heap, [1, 0, 0, 0, 0]);
	}

	#[test]
	fn should_write_u32_max_correctly_into_le() {
		// given
		let mut heap = vec![0; 5];

		// when
		FreeingBumpHeapAllocator::write_u32_into_le_bytes(u32::max_value(), &mut heap[0..4]);

		// then
		assert_eq!(heap, [255, 255, 255, 255, 0]);
	}

	#[test]
	fn should_get_item_size_from_index() {
		// given
		let index = 0;

		// when
		let item_size = FreeingBumpHeapAllocator::get_item_size_from_index(index);

		// then
		assert_eq!(item_size, 8);
	}

	#[test]
	fn should_get_max_item_size_from_index() {
		// given
		let index = 21;

		// when
		let item_size = FreeingBumpHeapAllocator::get_item_size_from_index(index);

		// then
		assert_eq!(item_size as u32, MAX_POSSIBLE_ALLOCATION);
	}

}
