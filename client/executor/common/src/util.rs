// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Utilities used by all backends

use crate::error::Result;
use sp_wasm_interface::Pointer;
use std::ops::Range;

/// Construct a range from an offset to a data length after the offset.
/// Returns None if the end of the range would exceed some maximum offset.
pub fn checked_range(offset: usize, len: usize, max: usize) -> Option<Range<usize>> {
	let end = offset.checked_add(len)?;
	if end <= max {
		Some(offset..end)
	} else {
		None
	}
}

/// Provides safe memory access interface using an external buffer
pub trait MemoryTransfer {
	/// Read data from a slice of memory into a newly allocated buffer.
	///
	/// Returns an error if the read would go out of the memory bounds.
	fn read(&self, source_addr: Pointer<u8>, size: usize) -> Result<Vec<u8>>;

	/// Read data from a slice of memory into a destination buffer.
	///
	/// Returns an error if the read would go out of the memory bounds.
	fn read_into(&self, source_addr: Pointer<u8>, destination: &mut [u8]) -> Result<()>;

	/// Write data to a slice of memory.
	///
	/// Returns an error if the write would go out of the memory bounds.
	fn write_from(&self, dest_addr: Pointer<u8>, source: &[u8]) -> Result<()>;
}
