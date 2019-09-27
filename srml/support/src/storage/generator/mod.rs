// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Generators are a set of trait on which storage traits are implemented.
//!
//! (i.e. implementing the generator for StorageValue on a type will automatically derive the
//! implementation of StorageValue for this type).
//!
//! They are used by `decl_storage`.

mod linked_map;
mod map;
mod double_map;
mod value;

pub use linked_map::{StorageLinkedMap, Enumerator, Linkage};
pub use map::StorageMap;
pub use double_map::StorageDoubleMap;
pub use value::StorageValue;
