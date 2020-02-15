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
//! The heap is a continuous linear memory and chunks are allocated using a bump allocator.
//!
//! ```ignore
//! +-------------+-------------------------------------------------+
//! | <allocated> | <unallocated>                                   |
//! +-------------+-------------------------------------------------+
//!               ^
//!               |_ bumper
//! ```
//!
//! Only allocations with sizes of power of two can be allocated. If the incoming request has a non
//! power of two size it is increased to the nearest power of two. The power of two of size is
//! referred as **an order**.
//!
//! Each allocation has a header immediately preceding to it. The header is always 8 bytes and can
//! be of two types: free and occupied.
//!
//! For implementing freeing we maintain a linked lists for each order. The maximum supported
//! allocation size is capped, therefore the number of orders and thus the linked lists is as well
//! limited.
//!
//! When the allocator serves an allocation request it first checks the linked list for the respective
//! order. If it doesn't have any free chunks, the allocator requests memory from the bump allocator.
//! In any case the order is stored in the header of the allocation.
//!
//! Upon deallocation we get the order of the allocation from its header and then add that
//! allocation to the linked list for the respective order.

use crate::Error;
use sp_std::{convert::{TryFrom, TryInto}, ops::{Range, Index, IndexMut}};
use sp_wasm_interface::{Pointer, WordSize};

/// The minimal alignment guaranteed by this allocator. The alignment of 8 is chosen because it is
/// the alignment guaranteed by wasm32.
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
const HEADER_SIZE: u32 = 8;

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

/// The exponent for the power of two sized block adjusted to the minimum size.
///
/// This way, if `MIN_POSSIBLE_ALLOCATION == 8`, we would get:
///
/// power_of_two_size | order
/// 8                 | 0
/// 16                | 1
/// 32                | 2
/// 64                | 3
///
/// and so on.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct Order(u32);

impl Order {
	/// Create `Order` object from a raw order.
	///
	/// Returns `Err` if it is greater than the maximum supported order.
	fn from_raw(order: u32) -> Result<Self, Error> {
		if order < N as u32 {
			Ok(Self(order))
		} else {
			Err(error("invalid order"))
		}
	}

	/// Compute the order by the given size
	///
	/// The size is clamped, so that the following holds:
	///
	/// `MIN_POSSIBLE_ALLOCATION <= size <= MAX_POSSIBLE_ALLOCATION`
	fn from_size(size: u32) -> Result<Self, Error> {
		let clamped_size = if size > MAX_POSSIBLE_ALLOCATION {
			return Err(Error::RequestedAllocationTooLarge);
		} else if size < MIN_POSSIBLE_ALLOCATION {
			MIN_POSSIBLE_ALLOCATION
		} else {
			size
		};

		// Round the clamped size to the next power of two.
		//
		// It returns the unchanged value if the value is already a power of two.
		let power_of_two_size = clamped_size.next_power_of_two();

		// Compute the number of trailing zeroes to get the order. We adjust it by the number of
		// trailing zeroes in the minimum possible allocation.
		let order = power_of_two_size.trailing_zeros() - MIN_POSSIBLE_ALLOCATION.trailing_zeros();

		Ok(Self(order))
	}

	/// Returns the corresponding size for this order.
	///
	/// Note that it is always a power of two.
	fn size(&self) -> u32 {
		MIN_POSSIBLE_ALLOCATION << self.0
	}

	/// Extract the order as `u32`.
	fn into_raw(self) -> u32 {
		self.0
	}
}

/// A marker for denoting the end of the linked list.
const EMPTY_MARKER: u32 = u32::max_value();

/// A link between headers in the free list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Link {
	/// Null, denotes that there is no next element.
	Null,
	/// Link to the next element represented as a pointer to the a header.
	Ptr(u32),
}

impl Link {
	/// Creates a link from raw value.
	fn from_raw(raw: u32) -> Self {
		if raw != EMPTY_MARKER {
			Self::Ptr(raw)
		} else {
			Self::Null
		}
	}

	/// Converts this link into a raw u32.
	fn into_raw(self) -> u32 {
		match self {
			Self::Null => EMPTY_MARKER,
			Self::Ptr(ptr) => ptr,
		}
	}
}

/// A header of an allocation.
///
/// The header is encoded in memory as follows.
///
/// ## Free header
///
/// ```ignore
/// 64             32                  0
//  +--------------+-------------------+
/// |            0 | next element link |
/// +--------------+-------------------+
/// ```
///
/// ## Occupied header
///
/// ```ignore
/// 64             32                  0
//  +--------------+-------------------+
/// |            1 |             order |
/// +--------------+-------------------+
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
enum Header {
	/// A free header contains a link to the next element to form a free linked list.
	Free(Link),
	/// An occupied header has attached order to know in which free list we should put the
	/// allocation upon deallocation.
	Occupied(Order),
}

impl Header {
	fn read_from<M: Memory + ?Sized>(memory: &M, header_ptr: u32) -> Result<Self, Error> {
		let raw_header = memory.read_le_u64(header_ptr)?;

		// Check if the header represents an occupied or free allocation and extract the header data
		// by trimming (and discarding) the high bits.
		let occupied = raw_header & 0x00000001_00000000 != 0;
		let header_data = raw_header as u32;

		Ok(if occupied {
			Self::Occupied(Order::from_raw(header_data)?)
		} else {
			Self::Free(Link::from_raw(header_data))
		})
	}

	/// Write out this header to memory.
	fn write_into<M: Memory + ?Sized>(&self, memory: &mut M, header_ptr: u32) -> Result<(), Error> {
		let (header_data, occupied_mask) = match *self {
			Self::Occupied(order) => (order.into_raw(), 0x00000001_00000000),
			Self::Free(link) => (link.into_raw(), 0x00000000_00000000),
		};
		let raw_header = header_data as u64 | occupied_mask;
		memory.write_le_u64(header_ptr, raw_header)?;
		Ok(())
	}

	/// Returns the order of the allocation if this is an occupied header.
	fn into_occupied(self) -> Option<Order> {
		match self {
			Self::Occupied(order) => Some(order),
			_ => None,
		}
	}

	/// Returns the link to the next element in the free list if this is a free header.
	fn into_free(self) -> Option<Link> {
		match self {
			Self::Free(link) => Some(link),
			_ => None,
		}
	}
}

/// This struct represents a collection of intrusive linked lists for each order.
struct FreeLists {
	heads: [Link; N],
}

impl FreeLists {
	/// Creates the free empty lists.
	fn new() -> Self {
		Self {
			heads: [Link::Null; N]
		}
	}

	/// Replaces a given link for the specified order and returns the old one.
	fn replace(&mut self, order: Order, new: Link) -> Link {
		let prev = self[order];
		self[order] = new;
		prev
	}
}

impl Index<Order> for FreeLists {
	type Output = Link;
	fn index(&self, index: Order) -> &Link {
		&self.heads[index.0 as usize]
	}
}

impl IndexMut<Order> for FreeLists {
	fn index_mut(&mut self, index: Order) -> &mut Link {
		&mut self.heads[index.0 as usize]
	}
}

/// An implementation of freeing bump allocator.
///
/// Refer to the module-level documentation for further details.
pub struct FreeingBumpHeapAllocator {
	bumper: u32,
	free_lists: FreeLists,
	total_size: u32,
}

impl FreeingBumpHeapAllocator {
	/// Creates a new allocation heap which follows a freeing-bump strategy.
	/// The maximum size which can be allocated at once is 16 MiB.
	///
	/// # Arguments
	///
	/// - `heap_base` - the offset from the beginning of the linear memory where the heap starts.
	pub fn new(heap_base: u32) -> Self {
		let aligned_heap_base = (heap_base + ALIGNMENT - 1) / ALIGNMENT * ALIGNMENT;

		FreeingBumpHeapAllocator {
			bumper: aligned_heap_base,
			free_lists: FreeLists::new(),
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
	pub fn allocate<M: Memory + ?Sized>(
		&mut self,
		mem: &mut M,
		size: WordSize,
	) -> Result<Pointer<u8>, Error> {
		let order = Order::from_size(size)?;

		let header_ptr: u32 = match self.free_lists[order] {
			Link::Ptr(header_ptr) => {
				assert!(
					header_ptr + order.size() + HEADER_SIZE <= mem.size(),
					"Pointer is looked up in list of free entries, into which
					only valid values are inserted; qed"
				);

				// Remove this header from the free list.
				let next_free = Header::read_from(mem, header_ptr)?
					.into_free()
					.ok_or_else(|| error("free list points to a occupied header"))?;
				self.free_lists[order] = next_free;

				header_ptr
			}
			Link::Null => {
				// Corresponding free list is empty. Allocate a new item.
				self.bump(order.size() + HEADER_SIZE, mem.size())?
			}
		};

		// Write the order in the occupied header.
		Header::Occupied(order).write_into(mem, header_ptr)?;

		self.total_size += order.size() + HEADER_SIZE;
		trace!("Heap size is {} bytes after allocation", self.total_size);

		Ok(Pointer::new(header_ptr + HEADER_SIZE))
	}

	/// Deallocates the space which was allocated for a pointer.
	///
	/// # Arguments
	///
	/// - `mem` - a slice representing the linear memory on which this allocator operates.
	/// - `ptr` - pointer to the allocated chunk
	pub fn deallocate<M: Memory + ?Sized>(&mut self, mem: &mut M, ptr: Pointer<u8>) -> Result<(), Error> {
		let header_ptr = u32::from(ptr)
			.checked_sub(HEADER_SIZE)
			.ok_or_else(|| error("Invalid pointer for deallocation"))?;

		let order = Header::read_from(mem, header_ptr)?
			.into_occupied()
			.ok_or_else(|| error("the allocation points to an empty header"))?;

		// Update the just freed header and knit it back to the free list.
		let prev_head = self.free_lists.replace(order, Link::Ptr(header_ptr));
		Header::Free(prev_head).write_into(mem, header_ptr)?;

		// Do the total_size book keeping.
		self.total_size = self
			.total_size
			.checked_sub(order.size() + HEADER_SIZE)
			.ok_or_else(|| error("Unable to subtract from total heap size without overflow"))?;
		trace!("Heap size is {} bytes after deallocation", self.total_size);

		Ok(())
	}

	/// Increases the `bumper` by `size`.
	///
	/// Returns the `bumper` from before the increase.
	/// Returns an `Error::AllocatorOutOfSpace` if the operation
	/// would exhaust the heap.
	fn bump(&mut self, size: u32, heap_end: u32) -> Result<u32, Error> {
		if self.bumper + size > heap_end {
			return Err(Error::AllocatorOutOfSpace);
		}

		let res = self.bumper;
		self.bumper += size;
		Ok(res)
	}
}

/// A trait for abstraction of accesses to linear memory.
pub trait Memory {
	/// Read a u64 from the heap in LE form. Used to read heap allocation prefixes.
	fn read_le_u64(&self, ptr: u32) -> Result<u64, Error>;
	/// Write a u64 to the heap in LE form. Used to write heap allocation prefixes.
	fn write_le_u64(&mut self, ptr: u32, val: u64) -> Result<(), Error>;
	/// Returns the full size of the memory.
	fn size(&self) -> u32;
}

impl Memory for [u8] {
	fn read_le_u64(&self, ptr: u32) -> Result<u64, Error> {
		let range =
			heap_range(ptr, 8, self.len()).ok_or_else(|| error("read out of heap bounds"))?;
		let bytes = self[range]
			.try_into()
			.expect("[u8] slice of length 8 must be convertible to [u8; 8]");
		Ok(u64::from_le_bytes(bytes))
	}
	fn write_le_u64(&mut self, ptr: u32, val: u64) -> Result<(), Error> {
		let range =
			heap_range(ptr, 8, self.len()).ok_or_else(|| error("write out of heap bounds"))?;
		let bytes = val.to_le_bytes();
		&mut self[range].copy_from_slice(&bytes[..]);
		Ok(())
	}
	fn size(&self) -> u32 {
		u32::try_from(self.len()).expect("size of Wasm linear memory is <2^32; qed")
	}
}

fn heap_range(offset: u32, length: u32, heap_len: usize) -> Option<Range<usize>> {
	let start = offset as usize;
	let end = offset.checked_add(length)? as usize;
	if end <= heap_len {
		Some(start..end)
	} else {
		None
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
		// returned pointer must start right after `HEADER_SIZE`
		assert_eq!(ptr, to_pointer(HEADER_SIZE));
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
		assert_eq!(ptr1, to_pointer(HEADER_SIZE));

		// the prefix of 8 bytes + the content of ptr1 padded to the lowest possible
		// item size of 8 bytes + the prefix of ptr1
		assert_eq!(ptr2, to_pointer(24));

		// ptr2 + its content of 16 bytes + the prefix of 8 bytes
		assert_eq!(ptr3, to_pointer(24 + 16 + HEADER_SIZE));
	}

	#[test]
	fn should_free_properly() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(0);
		let ptr1 = heap.allocate(&mut mem[..], 1).unwrap();
		// the prefix of 8 bytes is prepended to the pointer
		assert_eq!(ptr1, to_pointer(HEADER_SIZE));

		let ptr2 = heap.allocate(&mut mem[..], 1).unwrap();
		// the prefix of 8 bytes + the content of ptr 1 is prepended to the pointer
		assert_eq!(ptr2, to_pointer(24));

		// when
		heap.deallocate(&mut mem[..], ptr2).unwrap();

		// then
		// then the heads table should contain a pointer to the
		// prefix of ptr2 in the leftmost entry
		assert_eq!(heap.free_lists.heads[0], Link::Ptr(u32::from(ptr2) - HEADER_SIZE));
	}

	#[test]
	fn should_deallocate_and_reallocate_properly() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let padded_offset = 16;
		let mut heap = FreeingBumpHeapAllocator::new(13);

		let ptr1 = heap.allocate(&mut mem[..], 1).unwrap();
		// the prefix of 8 bytes is prepended to the pointer
		assert_eq!(ptr1, to_pointer(padded_offset + HEADER_SIZE));

		let ptr2 = heap.allocate(&mut mem[..], 9).unwrap();
		// the padded_offset + the previously allocated ptr (8 bytes prefix +
		// 8 bytes content) + the prefix of 8 bytes which is prepended to the
		// current pointer
		assert_eq!(ptr2, to_pointer(padded_offset + 16 + HEADER_SIZE));

		// when
		heap.deallocate(&mut mem[..], ptr2).unwrap();
		let ptr3 = heap.allocate(&mut mem[..], 9).unwrap();

		// then
		// should have re-allocated
		assert_eq!(ptr3, to_pointer(padded_offset + 16 + HEADER_SIZE));
		assert_eq!(heap.free_lists.heads, [Link::Null; N]);
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
		assert_eq!(heap.free_lists.heads[0], Link::Ptr(u32::from(ptr3) - HEADER_SIZE));

		let ptr4 = heap.allocate(&mut mem[..], 8).unwrap();
		assert_eq!(ptr4, ptr3);

		assert_eq!(heap.free_lists.heads[0], Link::Ptr(u32::from(ptr2) - HEADER_SIZE));
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
		let ptr1 = heap.allocate(&mut mem[..], (PAGE_SIZE / 2) - HEADER_SIZE).unwrap();
		assert_eq!(ptr1, to_pointer(HEADER_SIZE));

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
		assert_eq!(ptr, to_pointer(HEADER_SIZE));
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
		assert_eq!(ptr1, to_pointer(HEADER_SIZE));
		heap.deallocate(&mut mem[..], ptr1).expect("failed freeing ptr1");
		assert_eq!(heap.total_size, 0);
		assert_eq!(heap.bumper, 40);

		let ptr2 = heap.allocate(&mut mem[..], 16).unwrap();
		assert_eq!(ptr2, to_pointer(48));
		heap.deallocate(&mut mem[..], ptr2).expect("failed freeing ptr2");
		assert_eq!(heap.total_size, 0);
		assert_eq!(heap.bumper, 64);

		// when
		// the `bumper` value is equal to `size` here and any
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
		assert_eq!(heap.total_size, HEADER_SIZE + 16);
	}

	#[test]
	fn should_calculate_total_heap_size_to_zero() {
		// given
		let mut mem = [0u8; PAGE_SIZE as usize];
		let mut heap = FreeingBumpHeapAllocator::new(13);

		// when
		let ptr = heap.allocate(&mut mem[..], 42).unwrap();
		assert_eq!(ptr, to_pointer(16 + HEADER_SIZE));
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

		// when
		Memory::write_le_u64(mem.as_mut(), 40, 4480113).unwrap();

		// then
		let value = Memory::read_le_u64(mem.as_mut(), 40).unwrap();
		assert_eq!(value, 4480113);
	}

	#[test]
	fn should_get_item_size_from_order() {
		// given
		let raw_order = 0;

		// when
		let item_size = Order::from_raw(raw_order).unwrap().size();

		// then
		assert_eq!(item_size, 8);
	}

	#[test]
	fn should_get_max_item_size_from_index() {
		// given
		let raw_order = 21;

		// when
		let item_size = Order::from_raw(raw_order).unwrap().size();

		// then
		assert_eq!(item_size as u32, MAX_POSSIBLE_ALLOCATION);
	}

	#[test]
	fn deallocate_needs_to_maintain_linked_list() {
		let mut mem = [0u8; 8 * 2 * 4 + ALIGNMENT as usize];
		let mut heap = FreeingBumpHeapAllocator::new(0);

		// Allocate and free some pointers
		let ptrs = (0..4).map(|_| heap.allocate(&mut mem[..], 8).unwrap()).collect::<Vec<_>>();
		ptrs.into_iter().for_each(|ptr| heap.deallocate(&mut mem[..], ptr).unwrap());

		// Second time we should be able to allocate all of them again.
		let _ = (0..4).map(|_| heap.allocate(&mut mem[..], 8).unwrap()).collect::<Vec<_>>();
	}

	#[test]
	fn header_read_write() {
		let roundtrip = |header: Header| {
			let mut memory = [0u8; 32];
			header.write_into(memory.as_mut(), 0).unwrap();

			let read_header = Header::read_from(memory.as_mut(), 0).unwrap();
			assert_eq!(header, read_header);
		};

		roundtrip(Header::Occupied(Order(0)));
		roundtrip(Header::Occupied(Order(1)));
		roundtrip(Header::Free(Link::Null));
		roundtrip(Header::Free(Link::Ptr(0)));
		roundtrip(Header::Free(Link::Ptr(4)));
	}
}
