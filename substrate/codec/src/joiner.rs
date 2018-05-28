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

//! Trait

use core::iter::Extend;
use super::slicable::Slicable;

/// Trait to allow itself to be serialised into a value which can be extended
/// by bytes.
pub trait Joiner {
	fn and<V: Slicable + Sized>(self, value: &V) -> Self;
}

impl<T> Joiner for T where T: for<'a> Extend<&'a u8> {
	fn and<V: Slicable + Sized>(mut self, value: &V) -> Self {
		value.using_encoded(|s| self.extend(s));
		self
	}
}
