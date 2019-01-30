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

#![warn(missing_docs)]

//! This module implements a linear allocation heap.

pub struct Heap {
	end: u32,
	total_size: u32,
}

impl Heap {
	/// Construct new `Heap` struct.
	///
	/// Returns `Err` if the heap couldn't allocate required
	/// number of pages.
	///
	/// This could mean that wasm binary specifies memory
	/// limit and we are trying to allocate beyond that limit.
	pub fn new(reserved: u32) -> Self {
		Heap {
			end: reserved,
			total_size: 0,
		}
	}

	pub fn allocate(&mut self, size: u32) -> u32 {
		let r = self.end;
		self.end += size;
		let new_total_size = r + size;
		if new_total_size > self.total_size {
			if new_total_size / 1024  > self.total_size / 1024 {
				trace!(target: "wasm-heap", "Allocated over {} MB",  new_total_size / 1024 / 1024);
			}
			self.total_size = new_total_size;
		}
		r
	}

	pub fn deallocate(&mut self, _offset: u32) {
	}
}
