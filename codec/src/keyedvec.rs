// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Serialiser and prepender.

use Codec;
use core::iter::Extend;
use alloc::vec::Vec;

/// Trait to allow itself to be serialised and prepended by a given slice.
pub trait KeyedVec {
	fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8>;
}

impl<T: Codec> KeyedVec for T {
	fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8> {
		self.using_encoded(|slice| {
			let mut r = prepend_key.to_vec();
			r.extend(slice);
			r
		})
	}
}
