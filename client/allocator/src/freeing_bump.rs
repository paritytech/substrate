// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
//! limited. Currently, the maximum size of an allocation is 32 MiB.
//!
//! When the allocator serves an allocation request it first checks the linked list for the
//! respective order. If it doesn't have any free chunks, the allocator requests memory from the
//! bump allocator. In any case the order is stored in the header of the allocation.
//!
//! Upon deallocation we get the order of the allocation from its header and then add that
//! allocation to the linked list for the respective order.
//!
//! # Caveats
//!
//! This is a fast allocator but it is also dumb. There are specifically two main shortcomings
//! that the user should keep in mind:
//!
//! - Once the bump allocator space is exhausted, there is no way to reclaim the memory. This means
//!   that it's possible to end up in a situation where there are no live allocations yet a new
//!   allocation will fail.
//!
//!   Let's look into an example. Given a heap of 32 MiB. The user makes a 32 MiB allocation that we
//!   call `X` . Now the heap is full. Then user deallocates `X`. Since all the space in the bump
//!   allocator was consumed by the 32 MiB allocation, allocations of all sizes except 32 MiB will
//!   fail.
//!
//! - Sizes of allocations are rounded up to the nearest order. That is, an allocation of 2,00001
//!   MiB will be put into the bucket of 4 MiB. Therefore, any allocation of size `(N, 2N]` will
//!   take up to `2N`, thus assuming a uniform distribution of allocation sizes, the average amount
//!   in use of a `2N` space on the heap will be `(3N + ε) / 2`. So average utilization is going to
//!   be around 75% (`(3N + ε) / 2 / 2N`) meaning that around 25% of the space in allocation will be
//!   wasted. This is more pronounced (in terms of absolute heap amounts) with larger allocation
//!   sizes.

use crate::{Error, Memory, MAX_WASM_PAGES, PAGE_SIZE};
pub use sp_core::MAX_POSSIBLE_ALLOCATION;
use sp_wasm_interface::{Pointer, WordSize};
use std::{
	cmp::{max, min},
	mem,
	ops::{Index, IndexMut, Range},
};

/// The minimal alignment guaranteed by this allocator.
///
/// The alignment of 8 is chosen because it is the maximum size of a primitive type supported by the
/// target version of wasm32: i64's natural alignment is 8.
const ALIGNMENT: u32 = 8;

// Each pointer is prefixed with 8 bytes, which identify the list index
// to which it belongs.
const HEADER_SIZE: u32 = 8;

/// Create an allocator error.
fn error(msg: &'static str) -> Error {
	Error::Other(msg)
}

const LOG_TARGET: &str = "wasm-heap";

// The minimum possible allocation size is chosen to be 8 bytes because in that case we would have
// easier time to provide the guaranteed alignment of 8.
//
// The maximum possible allocation size is set in the primitives to 32MiB.
//
// N_ORDERS - represents the number of orders supported.
//
// This number corresponds to the number of powers between the minimum possible allocation and
// maximum possible allocation, or: 2^3...2^25 (both ends inclusive, hence 23).
const N_ORDERS: usize = 23;
const MIN_POSSIBLE_ALLOCATION: u32 = 8; // 2^3 bytes, 8 bytes

/// The exponent for the power of two sized block adjusted to the minimum size.
///
/// This way, if `MIN_POSSIBLE_ALLOCATION == 8`, we would get:
///
/// power_of_two_size | order
/// 8                 | 0
/// 16                | 1
/// 32                | 2
/// 64                | 3
/// ...
/// 16777216          | 21
/// 33554432          | 22
///
/// and so on.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct Order(u32);

impl Order {
	/// Create `Order` object from a raw order.
	///
	/// Returns `Err` if it is greater than the maximum supported order.
	fn from_raw(order: u32) -> Result<Self, Error> {
		if order < N_ORDERS as u32 {
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
			log::warn!(target: LOG_TARGET, "going to fail due to allocating {:?}", size);
			return Err(Error::RequestedAllocationTooLarge)
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

	/// Returns the corresponding size in bytes for this order.
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

/// A special magic value for a pointer in a link that denotes the end of the linked list.
const NIL_MARKER: u32 = u32::MAX;

/// A link between headers in the free list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Link {
	/// Nil, denotes that there is no next element.
	Nil,
	/// Link to the next element represented as a pointer to the a header.
	Ptr(u32),
}

impl Link {
	/// Creates a link from raw value.
	fn from_raw(raw: u32) -> Self {
		if raw != NIL_MARKER {
			Self::Ptr(raw)
		} else {
			Self::Nil
		}
	}

	/// Converts this link into a raw u32.
	fn into_raw(self) -> u32 {
		match self {
			Self::Nil => NIL_MARKER,
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
/// ## Occupied header
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
	/// Reads a header from memory.
	///
	/// Returns an error if the `header_ptr` is out of bounds of the linear memory or if the read
	/// header is corrupted (e.g. the order is incorrect).
	fn read_from(memory: &impl Memory, header_ptr: u32) -> Result<Self, Error> {
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
	///
	/// Returns an error if the `header_ptr` is out of bounds of the linear memory.
	fn write_into(&self, memory: &mut impl Memory, header_ptr: u32) -> Result<(), Error> {
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
	heads: [Link; N_ORDERS],
}

impl FreeLists {
	/// Creates the free empty lists.
	fn new() -> Self {
		Self { heads: [Link::Nil; N_ORDERS] }
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

/// Memory allocation stats gathered during the lifetime of the allocator.
#[derive(Clone, Debug, Default)]
#[non_exhaustive]
pub struct AllocationStats {
	/// The current number of bytes allocated.
	///
	/// This represents how many bytes are allocated *right now*.
	pub bytes_allocated: u32,

	/// The peak number of bytes ever allocated.
	///
	/// This is the maximum the `bytes_allocated` ever reached.
	pub bytes_allocated_peak: u32,

	/// The sum of every allocation ever made.
	///
	/// This increases every time a new allocation is made.
	pub bytes_allocated_sum: u128,

	/// The amount of address space (in bytes) used by the allocator.
	///
	/// This is calculated as the difference between the allocator's bumper
	/// and the heap base.
	///
	/// Currently the bumper's only ever incremented, so this is simultaneously
	/// the current value as well as the peak value.
	pub address_space_used: u32,
}

/// Convert the given `size` in bytes into the number of pages.
///
/// The returned number of pages is ensured to be big enough to hold memory with the given `size`.
///
/// Returns `None` if the number of pages to not fit into `u32`.
fn pages_from_size(size: u64) -> Option<u32> {
	u32::try_from((size + PAGE_SIZE as u64 - 1) / PAGE_SIZE as u64).ok()
}

/// An implementation of freeing bump allocator.
///
/// Refer to the module-level documentation for further details.
pub struct FreeingBumpHeapAllocator {
	original_heap_base: u32,
	bumper: u32,
	free_lists: FreeLists,
	poisoned: bool,
	last_observed_memory_size: u64,
	stats: AllocationStats,
}

impl Drop for FreeingBumpHeapAllocator {
	fn drop(&mut self) {
		log::debug!(target: LOG_TARGET, "allocator dropped: {:?}", self.stats)
	}
}

impl FreeingBumpHeapAllocator {
	/// Creates a new allocation heap which follows a freeing-bump strategy.
	///
	/// # Arguments
	///
	/// - `heap_base` - the offset from the beginning of the linear memory where the heap starts.
	pub fn new(heap_base: u32) -> Self {
		let aligned_heap_base = (heap_base + ALIGNMENT - 1) / ALIGNMENT * ALIGNMENT;

		FreeingBumpHeapAllocator {
			original_heap_base: aligned_heap_base,
			bumper: aligned_heap_base,
			free_lists: FreeLists::new(),
			poisoned: false,
			last_observed_memory_size: 0,
			stats: AllocationStats::default(),
		}
	}

	/// Gets requested number of bytes to allocate and returns a pointer.
	/// The maximum size which can be allocated at once is 32 MiB.
	/// There is no minimum size, but whatever size is passed into
	/// this function is rounded to the next power of two. If the requested
	/// size is below 8 bytes it will be rounded up to 8 bytes.
	///
	/// The identity or the type of the passed memory object does not matter. However, the size of
	/// memory cannot shrink compared to the memory passed in previous invocations.
	///
	/// NOTE: Once the allocator has returned an error all subsequent requests will return an error.
	///
	/// # Arguments
	///
	/// - `mem` - a slice representing the linear memory on which this allocator operates.
	/// - `size` - size in bytes of the allocation request
	pub fn allocate(
		&mut self,
		mem: &mut impl Memory,
		size: WordSize,
	) -> Result<Pointer<u8>, Error> {
		if self.poisoned {
			return Err(error("the allocator has been poisoned"))
		}

		let bomb = PoisonBomb { poisoned: &mut self.poisoned };

		Self::observe_memory_size(&mut self.last_observed_memory_size, mem)?;
		let order = Order::from_size(size)?;

		let header_ptr: u32 = match self.free_lists[order] {
			Link::Ptr(header_ptr) => {
				if (u64::from(header_ptr) + u64::from(order.size()) + u64::from(HEADER_SIZE)) >
					mem.size()
				{
					return Err(error("Invalid header pointer detected"))
				}

				// Remove this header from the free list.
				let next_free = Header::read_from(mem, header_ptr)?
					.into_free()
					.ok_or_else(|| error("free list points to a occupied header"))?;
				self.free_lists[order] = next_free;

				header_ptr
			},
			Link::Nil => {
				// Corresponding free list is empty. Allocate a new item.
				Self::bump(&mut self.bumper, order.size() + HEADER_SIZE, mem)?
			},
		};

		// Write the order in the occupied header.
		Header::Occupied(order).write_into(mem, header_ptr)?;

		self.stats.bytes_allocated += order.size() + HEADER_SIZE;
		self.stats.bytes_allocated_sum += u128::from(order.size() + HEADER_SIZE);
		self.stats.bytes_allocated_peak =
			max(self.stats.bytes_allocated_peak, self.stats.bytes_allocated);
		self.stats.address_space_used = self.bumper - self.original_heap_base;

		log::trace!(target: LOG_TARGET, "after allocation: {:?}", self.stats);

		bomb.disarm();
		Ok(Pointer::new(header_ptr + HEADER_SIZE))
	}

	/// Deallocates the space which was allocated for a pointer.
	///
	/// The identity or the type of the passed memory object does not matter. However, the size of
	/// memory cannot shrink compared to the memory passed in previous invocations.
	///
	/// NOTE: Once the allocator has returned an error all subsequent requests will return an error.
	///
	/// # Arguments
	///
	/// - `mem` - a slice representing the linear memory on which this allocator operates.
	/// - `ptr` - pointer to the allocated chunk
	pub fn deallocate(&mut self, mem: &mut impl Memory, ptr: Pointer<u8>) -> Result<(), Error> {
		if self.poisoned {
			return Err(error("the allocator has been poisoned"))
		}

		let bomb = PoisonBomb { poisoned: &mut self.poisoned };

		Self::observe_memory_size(&mut self.last_observed_memory_size, mem)?;

		let header_ptr = u32::from(ptr)
			.checked_sub(HEADER_SIZE)
			.ok_or_else(|| error("Invalid pointer for deallocation"))?;

		let order = Header::read_from(mem, header_ptr)?
			.into_occupied()
			.ok_or_else(|| error("the allocation points to an empty header"))?;

		// Update the just freed header and knit it back to the free list.
		let prev_head = self.free_lists.replace(order, Link::Ptr(header_ptr));
		Header::Free(prev_head).write_into(mem, header_ptr)?;

		self.stats.bytes_allocated = self
			.stats
			.bytes_allocated
			.checked_sub(order.size() + HEADER_SIZE)
			.ok_or_else(|| error("underflow of the currently allocated bytes count"))?;

		log::trace!("after deallocation: {:?}", self.stats);

		bomb.disarm();
		Ok(())
	}

	/// Returns the allocation stats for this allocator.
	pub fn stats(&self) -> AllocationStats {
		self.stats.clone()
	}

	/// Increases the `bumper` by `size`.
	///
	/// Returns the `bumper` from before the increase. Returns an `Error::AllocatorOutOfSpace` if
	/// the operation would exhaust the heap.
	fn bump(bumper: &mut u32, size: u32, memory: &mut impl Memory) -> Result<u32, Error> {
		let required_size = u64::from(*bumper) + u64::from(size);

		if required_size > memory.size() {
			let required_pages =
				pages_from_size(required_size).ok_or_else(|| Error::AllocatorOutOfSpace)?;

			let current_pages = memory.pages();
			let max_pages = memory.max_pages().unwrap_or(MAX_WASM_PAGES);
			debug_assert!(
				current_pages < required_pages,
				"current pages {current_pages} < required pages {required_pages}"
			);

			if current_pages >= max_pages {
				log::debug!(
					target: LOG_TARGET,
					"Wasm pages ({current_pages}) are already at the maximum.",
				);

				return Err(Error::AllocatorOutOfSpace)
			} else if required_pages > max_pages {
				log::debug!(
					target: LOG_TARGET,
					"Failed to grow memory from {current_pages} pages to at least {required_pages}\
						 pages due to the maximum limit of {max_pages} pages",
				);
				return Err(Error::AllocatorOutOfSpace)
			}

			// Ideally we want to double our current number of pages,
			// as long as it's less than the absolute maximum we can have.
			let next_pages = min(current_pages * 2, max_pages);
			// ...but if even more pages are required then try to allocate that many.
			let next_pages = max(next_pages, required_pages);

			if memory.grow(next_pages - current_pages).is_err() {
				log::error!(
					target: LOG_TARGET,
					"Failed to grow memory from {current_pages} pages to {next_pages} pages",
				);

				return Err(Error::AllocatorOutOfSpace)
			}

			debug_assert_eq!(memory.pages(), next_pages, "Number of pages should have increased!");
		}

		let res = *bumper;
		*bumper += size;
		Ok(res)
	}

	fn observe_memory_size(
		last_observed_memory_size: &mut u64,
		mem: &mut impl Memory,
	) -> Result<(), Error> {
		if mem.size() < *last_observed_memory_size {
			return Err(Error::MemoryShrinked)
		}
		*last_observed_memory_size = mem.size();
		Ok(())
	}
}

/// A trait for abstraction of accesses to a wasm linear memory. Used to read or modify the
/// allocation prefixes.
///
/// A wasm linear memory behaves similarly to a vector. The address space doesn't have holes and is
/// accessible up to the reported size.
///
/// The linear memory can grow in size with the wasm page granularity (64KiB), but it cannot shrink.
trait MemoryExt: Memory {
	/// Read a u64 from the heap in LE form. Returns an error if any of the bytes read are out of
	/// bounds.
	fn read_le_u64(&self, ptr: u32) -> Result<u64, Error> {
		self.with_access(|memory| {
			let range =
				heap_range(ptr, 8, memory.len()).ok_or_else(|| error("read out of heap bounds"))?;
			let bytes = memory[range]
				.try_into()
				.expect("[u8] slice of length 8 must be convertible to [u8; 8]");
			Ok(u64::from_le_bytes(bytes))
		})
	}

	/// Write a u64 to the heap in LE form. Returns an error if any of the bytes written are out of
	/// bounds.
	fn write_le_u64(&mut self, ptr: u32, val: u64) -> Result<(), Error> {
		self.with_access_mut(|memory| {
			let range = heap_range(ptr, 8, memory.len())
				.ok_or_else(|| error("write out of heap bounds"))?;
			let bytes = val.to_le_bytes();
			memory[range].copy_from_slice(&bytes[..]);
			Ok(())
		})
	}

	/// Returns the full size of the memory in bytes.
	fn size(&self) -> u64 {
		debug_assert!(self.pages() <= MAX_WASM_PAGES);

		self.pages() as u64 * PAGE_SIZE as u64
	}
}

impl<T: Memory> MemoryExt for T {}

fn heap_range(offset: u32, length: u32, heap_len: usize) -> Option<Range<usize>> {
	let start = offset as usize;
	let end = offset.checked_add(length)? as usize;
	if end <= heap_len {
		Some(start..end)
	} else {
		None
	}
}

/// A guard that will raise the poisoned flag on drop unless disarmed.
struct PoisonBomb<'a> {
	poisoned: &'a mut bool,
}

impl<'a> PoisonBomb<'a> {
	fn disarm(self) {
		mem::forget(self)
	}
}

impl<'a> Drop for PoisonBomb<'a> {
	fn drop(&mut self) {
		*self.poisoned = true;
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	/// Makes a pointer out of the given address.
	fn to_pointer(address: u32) -> Pointer<u8> {
		Pointer::new(address)
	}

	#[derive(Debug)]
	struct MemoryInstance {
		data: Vec<u8>,
		max_wasm_pages: u32,
	}

	impl MemoryInstance {
		fn with_pages(pages: u32) -> Self {
			Self { data: vec![0; (pages * PAGE_SIZE) as usize], max_wasm_pages: MAX_WASM_PAGES }
		}

		fn set_max_wasm_pages(&mut self, max_pages: u32) {
			self.max_wasm_pages = max_pages;
		}
	}

	impl Memory for MemoryInstance {
		fn with_access<R>(&self, run: impl FnOnce(&[u8]) -> R) -> R {
			run(&self.data)
		}

		fn with_access_mut<R>(&mut self, run: impl FnOnce(&mut [u8]) -> R) -> R {
			run(&mut self.data)
		}

		fn pages(&self) -> u32 {
			pages_from_size(self.data.len() as u64).unwrap()
		}

		fn max_pages(&self) -> Option<u32> {
			Some(self.max_wasm_pages)
		}

		fn grow(&mut self, pages: u32) -> Result<(), ()> {
			if self.pages() + pages > self.max_wasm_pages {
				Err(())
			} else {
				self.data.resize(((self.pages() + pages) * PAGE_SIZE) as usize, 0);
				Ok(())
			}
		}
	}

	#[test]
	fn test_pages_from_size() {
		assert_eq!(pages_from_size(0).unwrap(), 0);
		assert_eq!(pages_from_size(1).unwrap(), 1);
		assert_eq!(pages_from_size(65536).unwrap(), 1);
		assert_eq!(pages_from_size(65536 + 1).unwrap(), 2);
		assert_eq!(pages_from_size(2 * 65536).unwrap(), 2);
		assert_eq!(pages_from_size(2 * 65536 + 1).unwrap(), 3);
	}

	#[test]
	fn should_allocate_properly() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);

		// when
		let ptr = heap.allocate(&mut mem, 1).unwrap();

		// then
		// returned pointer must start right after `HEADER_SIZE`
		assert_eq!(ptr, to_pointer(HEADER_SIZE));
	}

	#[test]
	fn should_always_align_pointers_to_multiples_of_8() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(13);

		// when
		let ptr = heap.allocate(&mut mem, 1).unwrap();

		// then
		// the pointer must start at the next multiple of 8 from 13
		// + the prefix of 8 bytes.
		assert_eq!(ptr, to_pointer(24));
	}

	#[test]
	fn should_increment_pointers_properly() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);

		// when
		let ptr1 = heap.allocate(&mut mem, 1).unwrap();
		let ptr2 = heap.allocate(&mut mem, 9).unwrap();
		let ptr3 = heap.allocate(&mut mem, 1).unwrap();

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
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);
		let ptr1 = heap.allocate(&mut mem, 1).unwrap();
		// the prefix of 8 bytes is prepended to the pointer
		assert_eq!(ptr1, to_pointer(HEADER_SIZE));

		let ptr2 = heap.allocate(&mut mem, 1).unwrap();
		// the prefix of 8 bytes + the content of ptr 1 is prepended to the pointer
		assert_eq!(ptr2, to_pointer(24));

		// when
		heap.deallocate(&mut mem, ptr2).unwrap();

		// then
		// then the heads table should contain a pointer to the
		// prefix of ptr2 in the leftmost entry
		assert_eq!(heap.free_lists.heads[0], Link::Ptr(u32::from(ptr2) - HEADER_SIZE));
	}

	#[test]
	fn should_deallocate_and_reallocate_properly() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		let padded_offset = 16;
		let mut heap = FreeingBumpHeapAllocator::new(13);

		let ptr1 = heap.allocate(&mut mem, 1).unwrap();
		// the prefix of 8 bytes is prepended to the pointer
		assert_eq!(ptr1, to_pointer(padded_offset + HEADER_SIZE));

		let ptr2 = heap.allocate(&mut mem, 9).unwrap();
		// the padded_offset + the previously allocated ptr (8 bytes prefix +
		// 8 bytes content) + the prefix of 8 bytes which is prepended to the
		// current pointer
		assert_eq!(ptr2, to_pointer(padded_offset + 16 + HEADER_SIZE));

		// when
		heap.deallocate(&mut mem, ptr2).unwrap();
		let ptr3 = heap.allocate(&mut mem, 9).unwrap();

		// then
		// should have re-allocated
		assert_eq!(ptr3, to_pointer(padded_offset + 16 + HEADER_SIZE));
		assert_eq!(heap.free_lists.heads, [Link::Nil; N_ORDERS]);
	}

	#[test]
	fn should_build_linked_list_of_free_areas_properly() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);

		let ptr1 = heap.allocate(&mut mem, 8).unwrap();
		let ptr2 = heap.allocate(&mut mem, 8).unwrap();
		let ptr3 = heap.allocate(&mut mem, 8).unwrap();

		// when
		heap.deallocate(&mut mem, ptr1).unwrap();
		heap.deallocate(&mut mem, ptr2).unwrap();
		heap.deallocate(&mut mem, ptr3).unwrap();

		// then
		assert_eq!(heap.free_lists.heads[0], Link::Ptr(u32::from(ptr3) - HEADER_SIZE));

		let ptr4 = heap.allocate(&mut mem, 8).unwrap();
		assert_eq!(ptr4, ptr3);

		assert_eq!(heap.free_lists.heads[0], Link::Ptr(u32::from(ptr2) - HEADER_SIZE));
	}

	#[test]
	fn should_not_allocate_if_too_large() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		mem.set_max_wasm_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(13);

		// when
		let ptr = heap.allocate(&mut mem, PAGE_SIZE - 13);

		// then
		assert_eq!(Error::AllocatorOutOfSpace, ptr.unwrap_err());
	}

	#[test]
	fn should_not_allocate_if_full() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		mem.set_max_wasm_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);
		let ptr1 = heap.allocate(&mut mem, (PAGE_SIZE / 2) - HEADER_SIZE).unwrap();
		assert_eq!(ptr1, to_pointer(HEADER_SIZE));

		// when
		let ptr2 = heap.allocate(&mut mem, PAGE_SIZE / 2);

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
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);

		// when
		let ptr = heap.allocate(&mut mem, MAX_POSSIBLE_ALLOCATION).unwrap();

		// then
		assert_eq!(ptr, to_pointer(HEADER_SIZE));
	}

	#[test]
	fn should_not_allocate_if_requested_size_too_large() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);

		// when
		let ptr = heap.allocate(&mut mem, MAX_POSSIBLE_ALLOCATION + 1);

		// then
		assert_eq!(Error::RequestedAllocationTooLarge, ptr.unwrap_err());
	}

	#[test]
	fn should_return_error_when_bumper_greater_than_heap_size() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		mem.set_max_wasm_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);

		let mut ptrs = Vec::new();
		for _ in 0..(PAGE_SIZE as usize / 40) {
			ptrs.push(heap.allocate(&mut mem, 32).expect("Allocate 32 byte"));
		}

		assert_eq!(heap.stats.bytes_allocated, PAGE_SIZE - 16);
		assert_eq!(heap.bumper, PAGE_SIZE - 16);

		ptrs.into_iter()
			.for_each(|ptr| heap.deallocate(&mut mem, ptr).expect("Deallocate 32 byte"));

		assert_eq!(heap.stats.bytes_allocated, 0);
		assert_eq!(heap.stats.bytes_allocated_peak, PAGE_SIZE - 16);
		assert_eq!(heap.bumper, PAGE_SIZE - 16);

		// Allocate another 8 byte to use the full heap.
		heap.allocate(&mut mem, 8).expect("Allocate 8 byte");

		// when
		// the `bumper` value is equal to `size` here and any
		// further allocation which would increment the bumper must fail.
		// we try to allocate 8 bytes here, which will increment the
		// bumper since no 8 byte item has been freed before.
		assert_eq!(heap.bumper as u64, mem.size());
		let ptr = heap.allocate(&mut mem, 8);

		// then
		assert_eq!(Error::AllocatorOutOfSpace, ptr.unwrap_err());
	}

	#[test]
	fn should_include_prefixes_in_total_heap_size() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(1);

		// when
		// an item size of 16 must be used then
		heap.allocate(&mut mem, 9).unwrap();

		// then
		assert_eq!(heap.stats.bytes_allocated, HEADER_SIZE + 16);
	}

	#[test]
	fn should_calculate_total_heap_size_to_zero() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(13);

		// when
		let ptr = heap.allocate(&mut mem, 42).unwrap();
		assert_eq!(ptr, to_pointer(16 + HEADER_SIZE));
		heap.deallocate(&mut mem, ptr).unwrap();

		// then
		assert_eq!(heap.stats.bytes_allocated, 0);
	}

	#[test]
	fn should_calculate_total_size_of_zero() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(19);

		// when
		for _ in 1..10 {
			let ptr = heap.allocate(&mut mem, 42).unwrap();
			heap.deallocate(&mut mem, ptr).unwrap();
		}

		// then
		assert_eq!(heap.stats.bytes_allocated, 0);
	}

	#[test]
	fn should_read_and_write_u64_correctly() {
		// given
		let mut mem = MemoryInstance::with_pages(1);

		// when
		mem.write_le_u64(40, 4480113).unwrap();

		// then
		let value = MemoryExt::read_le_u64(&mut mem, 40).unwrap();
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
		let raw_order = 22;

		// when
		let item_size = Order::from_raw(raw_order).unwrap().size();

		// then
		assert_eq!(item_size as u32, MAX_POSSIBLE_ALLOCATION);
	}

	#[test]
	fn deallocate_needs_to_maintain_linked_list() {
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);

		// Allocate and free some pointers
		let ptrs = (0..4).map(|_| heap.allocate(&mut mem, 8).unwrap()).collect::<Vec<_>>();
		ptrs.iter().rev().for_each(|ptr| heap.deallocate(&mut mem, *ptr).unwrap());

		// Second time we should be able to allocate all of them again and get the same pointers!
		let new_ptrs = (0..4).map(|_| heap.allocate(&mut mem, 8).unwrap()).collect::<Vec<_>>();
		assert_eq!(ptrs, new_ptrs);
	}

	#[test]
	fn header_read_write() {
		let roundtrip = |header: Header| {
			let mut memory = MemoryInstance::with_pages(1);
			header.write_into(&mut memory, 0).unwrap();

			let read_header = Header::read_from(&memory, 0).unwrap();
			assert_eq!(header, read_header);
		};

		roundtrip(Header::Occupied(Order(0)));
		roundtrip(Header::Occupied(Order(1)));
		roundtrip(Header::Free(Link::Nil));
		roundtrip(Header::Free(Link::Ptr(0)));
		roundtrip(Header::Free(Link::Ptr(4)));
	}

	#[test]
	fn poison_oom() {
		// given
		let mut mem = MemoryInstance::with_pages(1);
		mem.set_max_wasm_pages(1);

		let mut heap = FreeingBumpHeapAllocator::new(0);

		// when
		let alloc_ptr = heap.allocate(&mut mem, PAGE_SIZE / 2).unwrap();
		assert_eq!(Error::AllocatorOutOfSpace, heap.allocate(&mut mem, PAGE_SIZE).unwrap_err());

		// then
		assert!(heap.poisoned);
		assert!(heap.deallocate(&mut mem, alloc_ptr).is_err());
	}

	#[test]
	fn test_n_orders() {
		// Test that N_ORDERS is consistent with min and max possible allocation.
		assert_eq!(
			MIN_POSSIBLE_ALLOCATION * 2u32.pow(N_ORDERS as u32 - 1),
			MAX_POSSIBLE_ALLOCATION
		);
	}

	#[test]
	fn accepts_growing_memory() {
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);

		heap.allocate(&mut mem, PAGE_SIZE / 2).unwrap();
		heap.allocate(&mut mem, PAGE_SIZE / 2).unwrap();

		mem.grow(1).unwrap();

		heap.allocate(&mut mem, PAGE_SIZE / 2).unwrap();
	}

	#[test]
	fn doesnt_accept_shrinking_memory() {
		let mut mem = MemoryInstance::with_pages(2);
		let mut heap = FreeingBumpHeapAllocator::new(0);

		heap.allocate(&mut mem, PAGE_SIZE / 2).unwrap();

		mem.data.truncate(PAGE_SIZE as usize);

		match heap.allocate(&mut mem, PAGE_SIZE / 2).unwrap_err() {
			Error::MemoryShrinked => (),
			_ => panic!(),
		}
	}

	#[test]
	fn should_grow_memory_when_running_out_of_memory() {
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);

		assert_eq!(1, mem.pages());

		heap.allocate(&mut mem, PAGE_SIZE * 2).unwrap();

		assert_eq!(3, mem.pages());
	}

	#[test]
	fn modifying_the_header_leads_to_an_error() {
		let mut mem = MemoryInstance::with_pages(1);
		let mut heap = FreeingBumpHeapAllocator::new(0);

		let ptr = heap.allocate(&mut mem, 5).unwrap();

		heap.deallocate(&mut mem, ptr).unwrap();

		Header::Free(Link::Ptr(u32::MAX - 1))
			.write_into(&mut mem, u32::from(ptr) - HEADER_SIZE)
			.unwrap();

		heap.allocate(&mut mem, 5).unwrap();
		assert!(heap
			.allocate(&mut mem, 5)
			.unwrap_err()
			.to_string()
			.contains("Invalid header pointer"));
	}
}
