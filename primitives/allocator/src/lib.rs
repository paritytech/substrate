// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Collection of allocator implementations.
//!
//! This crate provides the following allocator implementations:
//! - A freeing-bump allocator: [`FreeingBumpHeapAllocator`](freeing_bump::FreeingBumpHeapAllocator)

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

use sp_std::convert::{TryFrom, TryInto};
use sp_std::ops::Range;

mod error;
mod freeing_bump;

pub use freeing_bump::FreeingBumpHeapAllocator;
pub use error::Error;
use error::error;

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
