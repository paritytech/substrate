// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
//! list to which it belongs. If it is not empty, we unlink the first item from
//! the linked list and then reset the 8 preceding bytes so they now record
//! the identity of the linked list.
//!
//! To deallocate we use the preceding 8 bytes of the allocation to knit
//! back the allocation into the linked list from the head.

use crate::Error;
use sp_std::{convert::{TryFrom, TryInto}, ops::Range};
use sp_wasm_interface::{Pointer, WordSize};

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

/// An implementation of freeing bump allocator.
///
/// Refer to the module-level documentation for further details.
pub struct FreeingBumpHeapAllocator {
	bumper: u32,
	heads: [u32; N],
	ptr_offset: u32,
	total_size: u32,
}

/// Create an allocator error.
fn error(msg: &'static str) -> Error {
	Error::Other(msg)
}

/// A custom "trace" implementation that is only activated when `feature = std`.
///
/// Uses `wasm-heap` as default target.
macro_rules! trace {
	( $( $args:expr ),+ ) => {
		sp_std::if_std! {
			log::trace!(target: "wasm-heap", $( $args ),+);
		}
	}
}

impl FreeingBumpHeapAllocator {
	/// Creates a new allocation heap which follows a freeing-bump strategy.
	/// The maximum size which can be allocated at once is 16 MiB.
	///
	/// # Arguments
	///
	/// - `heap_base` - the offset from the beginning of the linear memory where the heap starts.
	pub fn new(heap_base: u32) -> Self {
		// ptr_offset is the next alignment boundary on or after heap_base.
		let ptr_offset = (heap_base + ALIGNMENT - 1) / ALIGNMENT * ALIGNMENT;

		FreeingBumpHeapAllocator {
			bumper: 0,
			heads: [u32::max_value(); N],
			ptr_offset,
			total_size: 0,
		}
	}

	/// Gets requested number of bytes to allocate and returns a pointer.
	/// The maximum size which can be allocated at once is 16 MiB.
	/// There is no minimum size, but whatever size is passed into
	/// this function is rounded to the next power of two. If the requested
	/// size is below 8 bytes it will be rounded up to 8 bytes.
	///
	/// # Arguments
	///
	/// - `mem` - a slice representing the linear memory on which this allocator operates.
	/// - `size` - size in bytes of the allocation request
	pub fn allocate(&mut self, mem: &mut [u8], size: WordSize) -> Result<Pointer<u8>, Error> {
		let mem_size = u32::try_from(mem.len())
			.expect("size of Wasm linear memory is <2^32; qed");
		let max_heap_size = mem_size - self.ptr_offset;

		if size > MAX_POSSIBLE_ALLOCATION {
			return Err(Error::RequestedAllocationTooLarge);
		}

		let size = size.max(MIN_POSSIBLE_ALLOCATION);
		let item_size = size.next_power_of_two();
		if item_size + PREFIX_SIZE + self.total_size > max_heap_size {
			return Err(Error::AllocatorOutOfSpace);
		}

		let list_index = (item_size.trailing_zeros() - 3) as usize;
		let ptr: u32 = if self.heads[list_index] != u32::max_value() {
			// Something from the free list
			let ptr = self.heads[list_index];
			assert!(
				ptr + item_size + PREFIX_SIZE <= max_heap_size,
				"Pointer is looked up in list of free entries, into which
				only valid values are inserted; qed"
			);

			self.heads[list_index] = self.get_heap_u64(mem, ptr)?
				.try_into()
				.map_err(|_| error("read invalid free list pointer"))?;
			ptr
		} else {
			// Nothing to be freed. Bump.
			self.bump(item_size, max_heap_size)?
		};

		self.set_heap_u64(mem, ptr, list_index as u64)?;

		self.total_size = self.total_size + item_size + PREFIX_SIZE;
		trace!("Heap size is {} bytes after allocation", self.total_size);

		Ok(Pointer::new(self.ptr_offset + ptr + PREFIX_SIZE))
	}

	/// Deallocates the space which was allocated for a pointer.
	///
	/// # Arguments
	///
	/// - `mem` - a slice representing the linear memory on which this allocator operates.
	/// - `ptr` - pointer to the allocated chunk
	pub fn deallocate(&mut self, mem: &mut [u8], ptr: Pointer<u8>) -> Result<(), Error> {
		let ptr = u32::from(ptr) - self.ptr_offset;
		let ptr = ptr.checked_sub(PREFIX_SIZE).ok_or_else(||
			error("Invalid pointer for deallocation")
		)?;

		let list_index: usize = self.get_heap_u64(mem, ptr)?
			.try_into()
			.map_err(|_| error("read invalid list index"))?;
		if list_index > self.heads.len() {
			return Err(error("read invalid list index"));
		}
		self.set_heap_u64(mem, ptr, self.heads[list_index] as u64)?;
		self.heads[list_index] = ptr;

		let item_size = Self::get_item_size_from_index(list_index);
		self.total_size = self.total_size.checked_sub(item_size as u32 + PREFIX_SIZE)
			.ok_or_else(|| error("Unable to subtract from total heap size without overflow"))?;
		trace!("Heap size is {} bytes after deallocation", self.total_size);

		Ok(())
	}

	/// Increases the `bumper` by `item_size + PREFIX_SIZE`.
	///
	/// Returns the `bumper` from before the increase.
	/// Returns an `Error::AllocatorOutOfSpace` if the operation
	/// would exhaust the heap.
	fn bump(&mut self, item_size: u32, max_heap_size: u32) -> Result<u32, Error> {
		if self.bumper + PREFIX_SIZE + item_size > max_heap_size {
			return Err(Error::AllocatorOutOfSpace);
		}

		let res = self.bumper;
		self.bumper += item_size + PREFIX_SIZE;
		Ok(res)
	}

	fn get_item_size_from_index(index: usize) -> usize {
		// we shift 1 by three places, since the first possible item size is 8
		1 << 3 << index
	}

	// Read a u64 from the heap in LE form. Used to read heap allocation prefixes.
	fn get_heap_u64(&self, heap: &[u8], offset: u32) -> Result<u64, Error> {
		let range = self.heap_range(offset, 8, heap.len())
			.ok_or_else(|| error("read out of heap bounds"))?;
		let bytes = heap[range].try_into()
			.expect("[u8] slice of length 8 must be convertible to [u8; 8]");
		Ok(u64::from_le_bytes(bytes))
	}

	// Write a u64 to the heap in LE form. Used to write heap allocation prefixes.
	fn set_heap_u64(&self, heap: &mut [u8], offset: u32, val: u64) -> Result<(), Error> {
		let range = self.heap_range(offset, 8, heap.len())
			.ok_or_else(|| error("write out of heap bounds"))?;
		let bytes = val.to_le_bytes();
		&mut heap[range].copy_from_slice(&bytes[..]);
		Ok(())
	}

	fn heap_range(&self, offset: u32, length: u32, heap_len: usize) -> Option<Range<usize>> {
		let start = offset
			.checked_add(self.ptr_offset)?
			as usize;
		let end = offset
			.checked_add(self.ptr_offset)?
			.checked_add(length)?
			as usize;
		if end <= heap_len {
			Some(start..end)
		} else {
			None
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	const PAGE_SIZE: u32 = 65536;

	/// Makes a pointer out of the given address.
	fn to_pointer(address: u32) -> Pointer<u8> {
		Pointer::new(address)
	}

	#[test]
	fn should_allocate_properly() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(0);

		// when
		let ptr = heap.allocate(&mut mem[..], 1).unwrap();

		// then
		// returned pointer must start right after `PREFIX_SIZE`
		assert_eq!(ptr, to_pointer(PREFIX_SIZE));
	}

	#[test]
	fn should_always_align_pointers_to_multiples_of_8() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(13);

		// when
		let ptr = heap.allocate(&mut mem[..], 1).unwrap();

		// then
		// the pointer must start at the next multiple of 8 from 13
		// + the prefix of 8 bytes.
		assert_eq!(ptr, to_pointer(24));
	}

	#[test]
	fn should_increment_pointers_properly() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(0);

		// when
		let ptr1 = heap.allocate(&mut mem[..], 1).unwrap();
		let ptr2 = heap.allocate(&mut mem[..], 9).unwrap();
		let ptr3 = heap.allocate(&mut mem[..], 1).unwrap();

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
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(0);
		let ptr1 = heap.allocate(&mut mem[..], 1).unwrap();
		// the prefix of 8 bytes is prepended to the pointer
		assert_eq!(ptr1, to_pointer(PREFIX_SIZE));

		let ptr2 = heap.allocate(&mut mem[..], 1).unwrap();
		// the prefix of 8 bytes + the content of ptr 1 is prepended to the pointer
		assert_eq!(ptr2, to_pointer(24));

		// when
		heap.deallocate(&mut mem[..], ptr2).unwrap();

		// then
		// then the heads table should contain a pointer to the
		// prefix of ptr2 in the leftmost entry
		assert_eq!(heap.heads[0], u32::from(ptr2) - PREFIX_SIZE);
	}

	#[test]
	fn should_deallocate_and_reallocate_properly() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let padded_offset = 16;
		let mut heap = FreeingBumpHeapAllocator::new(13);

		let ptr1 = heap.allocate(&mut mem[..], 1).unwrap();
		// the prefix of 8 bytes is prepended to the pointer
		assert_eq!(ptr1, to_pointer(padded_offset + PREFIX_SIZE));

		let ptr2 = heap.allocate(&mut mem[..], 9).unwrap();
		// the padded_offset + the previously allocated ptr (8 bytes prefix +
		// 8 bytes content) + the prefix of 8 bytes which is prepended to the
		// current pointer
		assert_eq!(ptr2, to_pointer(padded_offset + 16 + PREFIX_SIZE));

		// when
		heap.deallocate(&mut mem[..], ptr2).unwrap();
		let ptr3 = heap.allocate(&mut mem[..], 9).unwrap();

		// then
		// should have re-allocated
		assert_eq!(ptr3, to_pointer(padded_offset + 16 + PREFIX_SIZE));
		assert_eq!(heap.heads, [u32::max_value(); N]);
	}

	#[test]
	fn should_build_linked_list_of_free_areas_properly() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(0);

		let ptr1 = heap.allocate(&mut mem[..], 8).unwrap();
		let ptr2 = heap.allocate(&mut mem[..], 8).unwrap();
		let ptr3 = heap.allocate(&mut mem[..], 8).unwrap();

		// when
		heap.deallocate(&mut mem[..], ptr1).unwrap();
		heap.deallocate(&mut mem[..], ptr2).unwrap();
		heap.deallocate(&mut mem[..], ptr3).unwrap();

		// then
		assert_eq!(heap.heads[0], u32::from(ptr3) - PREFIX_SIZE);

		let ptr4 = heap.allocate(&mut mem[..], 8).unwrap();
		assert_eq!(ptr4, ptr3);

		assert_eq!(heap.heads[0], u32::from(ptr2) - PREFIX_SIZE);
	}

	#[test]
	fn should_not_allocate_if_too_large() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(13);

		// when
		let ptr = heap.allocate(&mut mem[..], PAGE_SIZE - 13);

		// then
		match ptr.unwrap_err() {
			Error::AllocatorOutOfSpace => {},
			e => panic!("Expected allocator out of space error, got: {:?}", e),
		}
	}

	#[test]
	fn should_not_allocate_if_full() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(0);
		let ptr1 = heap.allocate(&mut mem[..], (PAGE_SIZE / 2) - PREFIX_SIZE).unwrap();
		assert_eq!(ptr1, to_pointer(PREFIX_SIZE));

		// when
		let ptr2 = heap.allocate(&mut mem[..], PAGE_SIZE / 2);

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
		let mut mem = vec![0u8; (MAX_POSSIBLE_ALLOCATION + PAGE_SIZE) as usize];
		let mut heap = FreeingBumpHeapAllocator::new(0);

		// when
		let ptr = heap.allocate(&mut mem[..], MAX_POSSIBLE_ALLOCATION).unwrap();

		// then
		assert_eq!(ptr, to_pointer(PREFIX_SIZE));
	}

	#[test]
	fn should_not_allocate_if_requested_size_too_large() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(0);

		// when
		let ptr = heap.allocate(&mut mem[..], MAX_POSSIBLE_ALLOCATION + 1);

		// then
		match ptr.unwrap_err() {
			Error::RequestedAllocationTooLarge => {},
			e => panic!("Expected allocation size too large error, got: {:?}", e),
		}
	}

	#[test]
	fn should_return_error_when_bumper_greater_than_heap_size() {
		// given
		let mut mem = [0u8; 64];
		let mut heap = FreeingBumpHeapAllocator::new(0);

		let ptr1 = heap.allocate(&mut mem[..], 32).unwrap();
		assert_eq!(ptr1, to_pointer(PREFIX_SIZE));
		heap.deallocate(&mut mem[..], ptr1).expect("failed freeing ptr1");
		assert_eq!(heap.total_size, 0);
		assert_eq!(heap.bumper, 40);

		let ptr2 = heap.allocate(&mut mem[..], 16).unwrap();
		assert_eq!(ptr2, to_pointer(48));
		heap.deallocate(&mut mem[..], ptr2).expect("failed freeing ptr2");
		assert_eq!(heap.total_size, 0);
		assert_eq!(heap.bumper, 64);

		// when
		// the `bumper` value is equal to `max_heap_size` here and any
		// further allocation which would increment the bumper must fail.
		// we try to allocate 8 bytes here, which will increment the
		// bumper since no 8 byte item has been allocated+freed before.
		let ptr = heap.allocate(&mut mem[..], 8);

		// then
		match ptr.unwrap_err() {
			Error::AllocatorOutOfSpace => {},
			e => panic!("Expected allocator out of space error, got: {:?}", e),
		}
	}

	#[test]
	fn should_include_prefixes_in_total_heap_size() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(1);

		// when
		// an item size of 16 must be used then
		heap.allocate(&mut mem[..], 9).unwrap();

		// then
		assert_eq!(heap.total_size, PREFIX_SIZE + 16);
	}

	#[test]
	fn should_calculate_total_heap_size_to_zero() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(13);

		// when
		let ptr = heap.allocate(&mut mem[..], 42).unwrap();
		assert_eq!(ptr, to_pointer(16 + PREFIX_SIZE));
		heap.deallocate(&mut mem[..], ptr).unwrap();

		// then
		assert_eq!(heap.total_size, 0);
	}

	#[test]
	fn should_calculate_total_size_of_zero() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(19);

		// when
		for _ in 1..10 {
			let ptr = heap.allocate(&mut mem[..], 42).unwrap();
			heap.deallocate(&mut mem[..], ptr).unwrap();
		}

		// then
		assert_eq!(heap.total_size, 0);
	}

	#[test]
	fn should_read_and_write_u64_correctly() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let heap = FreeingBumpHeapAllocator::new(16);

		// when
		heap.set_heap_u64(&mut mem[..], 40, 4480113).unwrap();

		// then
		let value = heap.get_heap_u64(&mut mem[..], 40).unwrap();
		assert_eq!(value, 4480113);
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

	#[test]
	fn deallocate_needs_to_maintain_linked_list() {
		let mut mem = [0u8; 8 * 2 * 4 + ALIGNMENT as usize];
		let mut heap = FreeingBumpHeapAllocator::new(0);

		// Allocate and free some pointers
		let ptrs = (0..4).map(|_| heap.allocate(&mut mem, 8).unwrap()).collect::<Vec<_>>();
		ptrs.into_iter().for_each(|ptr| heap.deallocate(&mut mem, ptr).unwrap());

		// Second time we should be able to allocate all of them again.
		let _ = (0..4).map(|_| heap.allocate(&mut mem, 8).unwrap()).collect::<Vec<_>>();
	}
}
