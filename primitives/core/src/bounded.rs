// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Bounded collection types.

pub mod bounded_btree_map;
pub mod bounded_btree_set;
pub mod bounded_vec;
pub mod weak_bounded_vec;

pub use bounded_btree_map::BoundedBTreeMap;
pub use bounded_btree_set::BoundedBTreeSet;
pub use bounded_vec::{BoundedSlice, BoundedVec};
pub use weak_bounded_vec::WeakBoundedVec;
