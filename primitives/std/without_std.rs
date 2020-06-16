// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

pub extern crate alloc;

pub use alloc::boxed;
pub use alloc::rc;
pub use alloc::sync;
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
