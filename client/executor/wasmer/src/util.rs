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

use std::convert::TryFrom;
use wasmer_runtime_core::memory::Memory;

pub fn write_memory(memory: &Memory, offset: u32, data: &[u8]) -> Result<(), ()> {
	let offset = offset as usize;
	let view = memory.view::<u8>();
	dbg!(view.len());
	for (i, v) in data.iter().enumerate() {
		let cell = view.get(offset + i).ok_or(())?;
		cell.set(*v);
	}
	Ok(())
}

pub fn read_memory(memory: &Memory, offset: u32, output: &mut [u8]) -> Result<(), ()> {
	let offset = offset as usize;
	let view = memory.view::<u8>();
	for (i, v) in output.iter_mut().enumerate() {
		*v = view.get(offset + i).ok_or(())?.get();
	}
	Ok(())
}

pub struct AllocatorMemory<'a>(pub &'a Memory);

impl<'a> sp_allocator::Memory for AllocatorMemory<'a> {
	fn read_le_u64(&self, ptr: u32) -> Result<u64, sp_allocator::Error> {
		let mut bytes = [0u8; 8];
		read_memory(self.0, ptr, &mut bytes)
			.map_err(|_| sp_allocator::Error::Other("Out of bounds memory read"))?;
		Ok(u64::from_le_bytes(bytes))
	}
	fn write_le_u64(&mut self, ptr: u32, val: u64) -> Result<(), sp_allocator::Error> {
		let bytes = val.to_le_bytes();
		write_memory(self.0, ptr, &bytes)
			.map_err(|_| sp_allocator::Error::Other("Out of bounds memory write"))?;
		Ok(())
	}
	fn size(&self) -> u32 {
		u32::try_from(self.0.size().bytes().0).expect("size of Wasm linear memory is <2^32; qed")
	}
}
