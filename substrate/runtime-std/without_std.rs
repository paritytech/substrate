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

#[cfg(feature = "nightly")]
extern crate alloc;
#[cfg(feature = "nightly")]
extern crate pwasm_libc;
#[cfg(feature = "nightly")]
extern crate pwasm_alloc;

pub use alloc::boxed;
pub use alloc::rc;
pub use alloc::vec;
pub use core::borrow;
pub use core::cell;
pub use core::clone;
pub use core::cmp;
pub use core::fmt;
pub use core::intrinsics;
pub use core::iter;
pub use core::marker;
pub use core::mem;
pub use core::num;
pub use core::ops;
pub use core::ptr;
pub use core::slice;

pub mod collections {
	pub use alloc::btree_map;
}
