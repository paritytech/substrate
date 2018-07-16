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

//! Implements a serialization and deserialization codec for simple marshalling.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

#[cfg(feature = "std")]
extern crate core;

extern crate arrayvec;

#[cfg(feature = "std")]
pub mod alloc {
	pub use std::boxed;
	pub use std::vec;
}

mod codec;
mod joiner;
mod keyedvec;

pub use self::codec::{Input, Output, Encode, Decode, Codec};
pub use self::joiner::Joiner;
pub use self::keyedvec::KeyedVec;
