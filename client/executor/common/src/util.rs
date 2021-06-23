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

/// Routines specific to Wasmer runtime. Since sandbox can be invoked from both
/// wasmi and wasmtime runtime executors, we need to have a way to deal with sanbox
/// backends right from the start.
#[cfg(feature = "wasmer-sandbox")]
pub mod wasmer {
	use std::{cell::RefCell, rc::Rc};

	/// In order to enforce memory access protocol to the backend memory we wrap it
	/// with a `RefCell` and provide a scoped access.
	#[derive(Debug, Clone)]
	pub struct MemoryRef {
		buffer: Rc<RefCell<wasmer::Memory>>,
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
		pub fn with_direct_access<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
			let buf = self.buffer.borrow();
			let slice = unsafe { core::slice::from_raw_parts(buf.data_ptr(), buf.data_size() as usize) };

			f(slice)
		}

		/// Provides direct mutable access to the underlying memory buffer.
		///
		/// # Panics
		///
		/// Any calls that requires either read or write access to memory
		/// made within the closure will panic. Proceed with caution.
		pub fn with_direct_access_mut<R, F: FnOnce(&mut [u8]) -> R>(&self, f: F) -> R {
			let buf = self.buffer.borrow_mut();
			let slice = unsafe { core::slice::from_raw_parts_mut(buf.data_ptr(), buf.data_size() as usize) };

			f(slice)
		}

		/// Clone the underlying memory object
		///
		/// # Safety
		///
		/// The sole purpose of `MemoryRef` is to protect the memory from uncontrolled
		/// access. By returning memory object "as is" we bypass all checks.
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
