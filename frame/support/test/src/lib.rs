// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Test crate for frame_support. Allow to make use of `frame_support::decl_storage`.
//! See tests directory.

// Make sure we fail compilation on warnings
#![warn(missing_docs)]
#![deny(warnings)]

/// The configuration trait
pub trait Trait {
	/// The runtime origin type.
	type Origin;
	/// The block number type.
	type BlockNumber;
}

frame_support::decl_module! {
	/// Some test module
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}
