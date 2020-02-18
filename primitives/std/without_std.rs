// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

pub extern crate alloc;

pub use alloc::boxed;
pub use alloc::rc;
pub use alloc::vec;
pub use core::any;
pub use core::cell;
pub use core::clone;
pub use core::cmp;
pub use core::convert;
pub use core::default;
pub use core::fmt;
pub use core::hash;
pub use core::iter;
pub use core::marker;
pub use core::mem;
pub use core::num;
pub use core::ops;
pub use core::ptr;
pub use core::result;
pub use core::slice;
// Allow interpreting vectors of bytes as strings, but not constructing them.
pub use core::str;
// We are trying to avoid certain things here, such as `core::string`
// (if you need `String` you are probably doing something wrong, since
// runtime doesn't require anything human readable).

pub mod collections {
	pub use alloc::collections::btree_map;
	pub use alloc::collections::btree_set;
	pub use alloc::collections::vec_deque;
}

pub mod borrow {
	pub use core::borrow::*;
	pub use alloc::borrow::*;
}
