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

//! Serialiser and prepender.

use runtime_support::prelude::*;
use slicable::Slicable;

/// Trait to allow itselg to be serialised and prepended by a given slice.
pub trait KeyedVec {
	fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8>;
}

macro_rules! impl_non_endians {
	( $( $t:ty ),* ) => { $(
		impl KeyedVec for $t {
			fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8> {
				let mut r = prepend_key.to_vec();
				r.extend_from_slice(&self[..]);
				r
			}
		}
	)* }
}

macro_rules! impl_endians {
	( $( $t:ty ),* ) => { $(
		impl KeyedVec for $t {
			fn to_keyed_vec(&self, prepend_key: &[u8]) -> Vec<u8> {
				self.as_slice_then(|slice| {
					let mut r = prepend_key.to_vec();
					r.extend_from_slice(slice);
					r
				})
			}
		}
	)* }
}

impl_endians!(u8, i8, u16, u32, u64, usize, i16, i32, i64, isize);
impl_non_endians!([u8; 1], [u8; 2], [u8; 3], [u8; 4], [u8; 5], [u8; 6], [u8; 7], [u8; 8],
	[u8; 10], [u8; 12], [u8; 14], [u8; 16], [u8; 20], [u8; 24], [u8; 28], [u8; 32], [u8; 40],
	[u8; 48], [u8; 56], [u8; 64], [u8; 80], [u8; 96], [u8; 112], [u8; 128]);
