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

//! Vec<u8> serialiser.

use runtime_support::prelude::*;
use slicable::Slicable;

/// Trait to allow itself to be serialised into a `Vec<u8>`
pub trait Joiner {
	fn join<T: Slicable + Sized>(self, value: &T) -> Self;
}

impl Joiner for Vec<u8> {
	fn join<T: Slicable + Sized>(mut self, value: &T) -> Vec<u8> {
		value.as_slice_then(|s| self.extend_from_slice(s));
		self
	}
}
