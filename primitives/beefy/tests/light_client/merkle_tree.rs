// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use std::marker::PhantomData;

#[derive(Debug)]
pub struct Root<T> {
	root: u32,
	_data: PhantomData<T>,
}

impl<T> Clone for Root<T> {
	fn clone(&self) -> Self {
		Self::new(self.root)
	}
}

impl<T> Root<T> {
	pub fn new(root: u32) -> Self {
		Self {
			root,
			_data: Default::default(),
		}
	}
}

impl<T> From<u32> for Root<T> {
	fn from(root: u32) -> Self {
		Self::new(root)
	}
}

impl<T> Eq for Root<T> {}
impl<T> PartialEq for Root<T> {
	fn eq(&self, other: &Self) -> bool {
		self.root == other.root
	}
}

#[derive(Debug, PartialEq, Eq)]
pub enum Proof<T, X> {
	ValidFor(Root<T>, X),
	Invalid(X),
}

impl<T, X> Proof<T, X> {
	pub fn is_valid(&self, root: &Root<T>) -> bool {
		matches!(self, Self::ValidFor(ref expected, _) if expected == root)
	}

	pub fn into_data(self) -> X {
		match self {
			Self::ValidFor(_, d) => d,
			Self::Invalid(d) => d,
		}
	}
}
