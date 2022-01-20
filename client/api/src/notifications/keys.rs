// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use super::*;

use sp_core::hexdisplay::HexDisplay;

pub(super) type Keys = Option<HashSet<StorageKey>>;
pub(super) type ChildKeys = Option<HashMap<StorageKey, Option<HashSet<StorageKey>>>>;

pub(super) struct PrintKeys<'a>(pub &'a Keys);
impl<'a> std::fmt::Debug for PrintKeys<'a> {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		if let Some(keys) = self.0 {
			fmt.debug_list().entries(keys.iter().map(HexDisplay::from)).finish()
		} else {
			write!(fmt, "None")
		}
	}
}

pub(super) struct PrintChildKeys<'a>(pub &'a ChildKeys);
impl<'a> std::fmt::Debug for PrintChildKeys<'a> {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		if let Some(map) = self.0 {
			fmt.debug_map()
				.entries(map.iter().map(|(key, values)| (HexDisplay::from(key), PrintKeys(values))))
				.finish()
		} else {
			write!(fmt, "None")
		}
	}
}
