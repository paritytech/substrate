// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! An u32 trait with "values" as impl'd types.

/// A u32 value, wrapped in a trait because we don't yet have const generics.
pub trait Value {
	/// The actual value represented by the impl'ing type.
	const VALUE: u32;
}
/// Type representing the value 0 for the `Value` trait.
pub struct _0; impl Value for _0 { const VALUE: u32 = 0; }
/// Type representing the value 1 for the `Value` trait.
pub struct _1; impl Value for _1 { const VALUE: u32 = 1; }
/// Type representing the value 2 for the `Value` trait.
pub struct _2; impl Value for _2 { const VALUE: u32 = 2; }
/// Type representing the value 3 for the `Value` trait.
pub struct _3; impl Value for _3 { const VALUE: u32 = 3; }
/// Type representing the value 4 for the `Value` trait.
pub struct _4; impl Value for _4 { const VALUE: u32 = 4; }
/// Type representing the value 5 for the `Value` trait.
pub struct _5; impl Value for _5 { const VALUE: u32 = 5; }
/// Type representing the value 6 for the `Value` trait.
pub struct _6; impl Value for _6 { const VALUE: u32 = 6; }
/// Type representing the value 7 for the `Value` trait.
pub struct _7; impl Value for _7 { const VALUE: u32 = 7; }
/// Type representing the value 8 for the `Value` trait.
pub struct _8; impl Value for _8 { const VALUE: u32 = 8; }
/// Type representing the value 9 for the `Value` trait.
pub struct _9; impl Value for _9 { const VALUE: u32 = 9; }
/// Type representing the value 10 for the `Value` trait.
pub struct _10; impl Value for _10 { const VALUE: u32 = 10; }
/// Type representing the value 11 for the `Value` trait.
pub struct _11; impl Value for _11 { const VALUE: u32 = 11; }
/// Type representing the value 12 for the `Value` trait.
pub struct _12; impl Value for _12 { const VALUE: u32 = 12; }
/// Type representing the value 13 for the `Value` trait.
pub struct _13; impl Value for _13 { const VALUE: u32 = 13; }
/// Type representing the value 14 for the `Value` trait.
pub struct _14; impl Value for _14 { const VALUE: u32 = 14; }
/// Type representing the value 15 for the `Value` trait.
pub struct _15; impl Value for _15 { const VALUE: u32 = 15; }
/// Type representing the value 16 for the `Value` trait.
pub struct _16; impl Value for _16 { const VALUE: u32 = 16; }
/// Type representing the value 24 for the `Value` trait.
pub struct _24; impl Value for _24 { const VALUE: u32 = 24; }
/// Type representing the value 32 for the `Value` trait.
pub struct _32; impl Value for _32 { const VALUE: u32 = 32; }
/// Type representing the value 40 for the `Value` trait.
pub struct _40; impl Value for _40 { const VALUE: u32 = 40; }
/// Type representing the value 48 for the `Value` trait.
pub struct _48; impl Value for _48 { const VALUE: u32 = 48; }
/// Type representing the value 56 for the `Value` trait.
pub struct _56; impl Value for _56 { const VALUE: u32 = 56; }
/// Type representing the value 64 for the `Value` trait.
pub struct _64; impl Value for _64 { const VALUE: u32 = 64; }
/// Type representing the value 80 for the `Value` trait.
pub struct _80; impl Value for _80 { const VALUE: u32 = 80; }
/// Type representing the value 96 for the `Value` trait.
pub struct _96; impl Value for _96 { const VALUE: u32 = 96; }
/// Type representing the value 112 for the `Value` trait.
pub struct _112; impl Value for _112 { const VALUE: u32 = 112; }
/// Type representing the value 128 for the `Value` trait.
pub struct _128; impl Value for _128 { const VALUE: u32 = 128; }
/// Type representing the value 160 for the `Value` trait.
pub struct _160; impl Value for _160 { const VALUE: u32 = 160; }
/// Type representing the value 192 for the `Value` trait.
pub struct _192; impl Value for _192 { const VALUE: u32 = 192; }
/// Type representing the value 224 for the `Value` trait.
pub struct _224; impl Value for _224 { const VALUE: u32 = 224; }
/// Type representing the value 256 for the `Value` trait.
pub struct _256; impl Value for _256 { const VALUE: u32 = 256; }
/// Type representing the value 384 for the `Value` trait.
pub struct _384; impl Value for _384 { const VALUE: u32 = 384; }
/// Type representing the value 512 for the `Value` trait.
pub struct _512; impl Value for _512 { const VALUE: u32 = 512; }
