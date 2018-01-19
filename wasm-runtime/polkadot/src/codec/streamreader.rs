// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Deserialiser.

use slicable::Slicable;

/// Simple deserialiser.
pub struct StreamReader<'a> {
	data: &'a[u8],
	offset: usize,
}

impl<'a> StreamReader<'a> {
	/// Create a new deserialiser based on the `data`.
	pub fn new(data: &'a[u8]) -> Self {
		StreamReader {
			data: data,
			offset: 0,
		}
	}

	/// Deserialise a single item from the data stream.
	pub fn read<T: Slicable>(&mut self) -> Option<T> {
		let size = T::size_of(&self.data[self.offset..])?;
		let new_offset = self.offset + size;
		let slice = &self.data[self.offset..new_offset];
		self.offset = new_offset;
		Slicable::from_slice(slice)
	}
}
/*
// Not in use yet
// TODO: introduce fn size_will_be(&self) -> usize; to Slicable trait and implement
struct StreamWriter<'a> {
	data: &'a mut[u8],
	offset: usize,
}

impl<'a> StreamWriter<'a> {
	pub fn new(data: &'a mut[u8]) -> Self {
		StreamWriter {
			data: data,
			offset: 0,
		}
	}
	pub fn write<T: Slicable>(&mut self, value: &T) -> bool {
		value.as_slice_then(|s| {
			let new_offset = self.offset + s.len();
			if self.data.len() <= new_offset {
				let slice = &mut self.data[self.offset..new_offset];
				self.offset = new_offset;
				slice.copy_from_slice(s);
				true
			} else {
				false
			}
		})
	}
}
*/
