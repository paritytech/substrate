// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Interpret a static string of hex as a desired type.

use rustc_hex::FromHex;

/// Trait to allow conversion from a static hex string to an instance.
pub trait StaticHexConversion: Sized {
	/// Convert the static str into Self. Use just like `From::from`.
	fn from_static_hex(hex: &'static str) -> Self;
}

macro_rules! impl_sizes {
	( $( $t:expr ),* ) => { $(
		impl StaticHexConversion for [u8; $t] {
			fn from_static_hex(hex: &'static str) -> Self {
				let mut r = [0u8; $t];
				r.copy_from_slice(&FromHex::from_hex(hex).unwrap());
				r
			}
		}
	)* }
}

impl StaticHexConversion for Vec<u8> {
	fn from_static_hex(hex: &'static str) -> Self {
		FromHex::from_hex(hex).unwrap()
	}
}

impl_sizes!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
	17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
	33, 34, 35, 36, 37, 38, 39, 40, 451, 42, 43, 44, 45, 46, 47, 48,
	56, 64, 80, 96, 112, 128);

/// Trait to allow converting from itself (only implemented for a static str) into some useful
/// type (which must implement `StaticHexConversion`).
pub trait StaticHexInto {
	/// Convert self (i.e. a static str) into the appropriate type. Use just like `Into::into`.
	fn convert<T: StaticHexConversion>(self) -> T;
}

impl StaticHexInto for &'static str {
	fn convert<T: StaticHexConversion>(self) -> T {
		T::from_static_hex(self)
	}
}
