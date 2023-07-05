// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

#[derive(Clone, Copy, Debug, derive_more::Display)]
pub enum SizeType {
	#[display(fmt = "empty")]
	Empty,
	#[display(fmt = "small")]
	Small,
	#[display(fmt = "medium")]
	Medium,
	#[display(fmt = "large")]
	Large,
	#[display(fmt = "full")]
	Full,
	#[display(fmt = "custom")]
	Custom(usize),
}

impl SizeType {
	pub fn transactions(&self) -> Option<usize> {
		match self {
			SizeType::Empty => Some(0),
			SizeType::Small => Some(10),
			SizeType::Medium => Some(100),
			SizeType::Large => Some(500),
			SizeType::Full => None,
			// Custom SizeType will use the `--transactions` input parameter
			SizeType::Custom(val) => Some(*val),
		}
	}
}
