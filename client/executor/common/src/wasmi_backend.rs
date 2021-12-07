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

//! Wasmi specific impls for sandbox

use wasmi::ImportResolver;
use sp_wasm_interface::Pointer;

use crate::{
	util::{MemoryTransfer, checked_range},
	error,
	sandbox::Imports,
};

impl ImportResolver for Imports {
	fn resolve_func(
		&self,
		module_name: &str,
		field_name: &str,
		signature: &::wasmi::Signature,
	) -> std::result::Result<wasmi::FuncRef, wasmi::Error> {
		let idx = self.func_by_name(module_name, field_name).ok_or_else(|| {
			wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name))
		})?;

		Ok(wasmi::FuncInstance::alloc_host(signature.clone(), idx.0))
	}

	fn resolve_memory(
		&self,
		module_name: &str,
		field_name: &str,
		_memory_type: &::wasmi::MemoryDescriptor,
	) -> std::result::Result<wasmi::MemoryRef, wasmi::Error> {
		let mem = self.memory_by_name(module_name, field_name).ok_or_else(|| {
			wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name))
		})?;

		let wrapper = mem.as_wasmi().ok_or_else(|| {
			wasmi::Error::Instantiation(format!(
				"Unsupported non-wasmi export {}:{}",
				module_name, field_name
			))
		})?;

		// Here we use inner memory reference only to resolve
		// the imports without accessing the memory contents.
		let mem = unsafe { wrapper.clone_inner() };

		Ok(mem)
	}

	fn resolve_global(
		&self,
		module_name: &str,
		field_name: &str,
		_global_type: &::wasmi::GlobalDescriptor,
	) -> std::result::Result<wasmi::GlobalRef, wasmi::Error> {
		Err(wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name)))
	}

	fn resolve_table(
		&self,
		module_name: &str,
		field_name: &str,
		_table_type: &::wasmi::TableDescriptor,
	) -> std::result::Result<wasmi::TableRef, wasmi::Error> {
		Err(wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name)))
	}
}


/// Wasmi provides direct access to its memory using slices.
///
/// This wrapper limits the scope where the slice can be taken to
#[derive(Debug, Clone)]
pub struct MemoryWrapper(::wasmi::MemoryRef);

impl MemoryWrapper {
	/// Take ownership of the memory region and return a wrapper object
	pub fn new(memory: ::wasmi::MemoryRef) -> Self {
		Self(memory)
	}

	/// Clone the underlying memory object
	///
	/// # Safety
	///
	/// The sole purpose of `MemoryRef` is to protect the memory from uncontrolled
	/// access. By returning the memory object "as is" we bypass all of the checks.
	///
	/// Intended to use only during module initialization.
	pub unsafe fn clone_inner(&self) -> ::wasmi::MemoryRef {
		self.0.clone()
	}
}

impl MemoryTransfer for MemoryWrapper {
	fn read(&self, source_addr: Pointer<u8>, size: usize) -> error::Result<Vec<u8>> {
		self.0.with_direct_access(|source| {
			let range = checked_range(source_addr.into(), size, source.len())
				.ok_or_else(|| error::Error::Other("memory read is out of bounds".into()))?;

			Ok(Vec::from(&source[range]))
		})
	}

	fn read_into(&self, source_addr: Pointer<u8>, destination: &mut [u8]) -> error::Result<()> {
		self.0.with_direct_access(|source| {
			let range = checked_range(source_addr.into(), destination.len(), source.len())
				.ok_or_else(|| error::Error::Other("memory read is out of bounds".into()))?;

			destination.copy_from_slice(&source[range]);
			Ok(())
		})
	}

	fn write_from(&self, dest_addr: Pointer<u8>, source: &[u8]) -> error::Result<()> {
		self.0.with_direct_access_mut(|destination| {
			let range = checked_range(dest_addr.into(), source.len(), destination.len())
				.ok_or_else(|| error::Error::Other("memory write is out of bounds".into()))?;

			destination[range].copy_from_slice(source);
			Ok(())
		})
	}
}
