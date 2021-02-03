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

#[derive(Debug, PartialEq, Eq)]
pub struct Public(pub u8);

impl From<u8> for Public {
	fn from(public: u8) -> Self {
		Self(public)
	}
}

#[derive(Debug)]
pub enum Signature {
	ValidFor(Public),
	Invalid,
}

impl Signature {
	pub fn is_valid_for(&self, public: &Public) -> bool {
		matches!(self, Self::ValidFor(ref p) if p == public)
	}
}
