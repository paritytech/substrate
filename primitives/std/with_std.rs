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

pub use std::alloc;
pub use std::any;
pub use std::borrow;
pub use std::boxed;
pub use std::cell;
pub use std::clone;
pub use std::cmp;
pub use std::convert;
pub use std::default;
pub use std::fmt;
pub use std::hash;
pub use std::iter;
pub use std::marker;
pub use std::mem;
pub use std::num;
pub use std::ops;
pub use std::ptr;
pub use std::rc;
pub use std::result;
pub use std::slice;
pub use std::str;
pub use std::vec;

pub mod collections {
	pub use std::collections::btree_map;
	pub use std::collections::btree_set;
	pub use std::collections::vec_deque;
}
