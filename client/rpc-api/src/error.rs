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

/// Base error code for RPC modules.
pub mod base {
	pub const AUTHOR: i32 = 1000;
	pub const SYSTEM: i32 = 2000;
	pub const CHAIN: i32 = 3000;
	pub const STATE: i32 = 4000;
	pub const OFFCHAIN: i32 = 5000;
	pub const DEV: i32 = 6000;
	pub const STATEMENT: i32 = 7000;
}
