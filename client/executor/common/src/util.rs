// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use std::ops::Range;
use wasmi::MemoryRef;
use crate::error::TransferError;

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

pub unsafe trait BufferProvider {
	/// Provide scoped read-only access to the underlying buffer
	fn scoped_access<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R;
}

unsafe impl<'a> BufferProvider for MemoryRef {
	fn scoped_access<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.with_direct_access(f)
	}
}

struct WasmiBufferProxyMut {
	memory: MemoryRef,
}

impl WasmiBufferProxyMut {
	pub fn transfer(&mut self, source: impl BufferProvider, source_offset: usize, dest_offset: usize, len: usize) -> Result<(), TransferError> {
		source.scoped_access(|source| {
			self.memory.with_direct_access_mut(|dest| {
				let src_range = checked_range(source_offset, len, source.len()).ok_or(TransferError::SourceTooSmall)?;
				let dst_range = checked_range(dest_offset, len, dest.len()).ok_or(TransferError::DestTooSmall)?;

				dest[dst_range].copy_from_slice(&source[src_range]);

				Ok(())
			})
		})
	}
}

/// Routines specific to Wasmer runtime. Since sandbox can be invoked from both
/// wasmi and wasmtime runtime executors, we need to have a way to deal with sanbox
/// backends right from the start.
#[cfg(feature = "wasmer-sandbox")]
pub mod wasmer {
	use std::{cell::{Ref, RefCell, RefMut}, rc::Rc};
	use crate::{error::TransferError, util::checked_range};
	use super::BufferProvider;

	/// In order to enforce memory access protocol to the backend memory 
	/// we wrap it with `RefCell` and provide a scoped access.
	#[derive(Debug, Clone)]
	pub struct MemoryRef {
		buffer: Rc<RefCell<wasmer::Memory>>,
	}

	/// Represents a scoped right to read the associated memory
	pub struct BufferProxy<'a> {
		guard: Ref<'a, wasmer::Memory>,
	}

	impl<'a> BufferProxy<'a> {
		/// Accept the ownership and created proxy object
		pub fn new(guard: Ref<'a, wasmer::Memory>) -> Self {
			Self {
				guard,
			}
		}
	}

	/// Represents a scoped right to access the associated memory
	pub struct BufferProxyMut<'a> {
		guard: RefMut<'a, wasmer::Memory>,
	}

	impl<'a> BufferProxyMut<'a> {
		/// Accept the ownership and created proxy object
		pub fn new(guard: RefMut<'a, wasmer::Memory>) -> Self {
			Self {
				guard,
			}
		}

		/// Copy the data between buffers at a specified location
		pub fn transfer(&mut self, source: impl BufferProvider, source_offset: usize, dest_offset: usize, len: usize) -> Result<(), TransferError> {
			source.scoped_access(|source| {
				// This is safe because we construct the slice from the same parts as
				// the memory region itself. We hold the lock to both of memory buffers,
				// so we shouldn't have issues even if we'd try to borrow the memory twice.
				let dest = unsafe {
					let memory = &* self.guard;
					core::slice::from_raw_parts_mut(memory.data_ptr(), memory.data_size() as usize)
				};

				let src_range = checked_range(source_offset, len, source.len()).ok_or(TransferError::SourceTooSmall)?;
				let dst_range = checked_range(dest_offset, len, dest.len()).ok_or(TransferError::DestTooSmall)?;

				dest[dst_range].copy_from_slice(&source[src_range]);

				Ok(())
			})
		}
	}

	unsafe impl<'a> BufferProvider for BufferProxy<'a> {
		fn scoped_access<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
			// This is safe because we construct the slice from the same parts as
			// the memory region itself. We hold the lock to both of memory buffers,
			// so we shouldn't have issues even if we'd try to borrow the memory twice.
			let buffer = unsafe {
				let memory = &* self.guard;
				core::slice::from_raw_parts(memory.data_ptr(), memory.data_size() as usize)
			};

			f(buffer)
		}
	}

	impl MemoryRef {
		/// Take ownership of the memory region and return a wrapper object
		pub fn new(memory: wasmer::Memory) -> Self {
			Self {
				buffer: Rc::new(RefCell::new(memory))
			}
		}

		/// Provides direct access to the underlying memory buffer.
		///
		/// # Panics
		///
		/// Any call that requires write access to memory made within
		/// the closure will panic.
		pub fn with_direct_access<R, F: FnOnce(&BufferProxy) -> R>(&self, f: F) -> R {
			let buf = self.buffer.borrow();
			f(&BufferProxy::new(buf))
		}

		/// Provides direct mutable access to the underlying memory buffer.
		///
		/// # Panics
		///
		/// Any calls that requires either read or write access to memory
		/// made within the closure will panic. Proceed with caution.
		pub fn with_direct_access_mut<R, F: FnOnce(&BufferProxyMut) -> R>(&self, f: F) -> R {
			let buf = self.buffer.borrow_mut();
			f(&BufferProxyMut::new(buf))
		}

		/// Clone the underlying memory object
		///
		/// # Safety
		///
		/// The sole purpose of `MemoryRef` is to protect the memory from uncontrolled
		/// access. By returning the memory object "as is" we bypass all of the checks.
		///
		/// Intended to use only during module initialization.
		///
		/// # Panics
		///
		/// Will panic if `MemoryRef` is currently in use.
		pub unsafe fn clone_inner(&mut self) -> wasmer::Memory {
			// We take exclusive lock to ensure that we're the only one here
			self.buffer.borrow_mut().clone()
		}
	}

}
