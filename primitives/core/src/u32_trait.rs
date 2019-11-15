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
/// Type representing the value 17 for the `Value` trait.
pub struct _17; impl Value for _17 { const VALUE: u32 = 17; }
/// Type representing the value 18 for the `Value` trait.
pub struct _18; impl Value for _18 { const VALUE: u32 = 18; }
/// Type representing the value 19 for the `Value` trait.
pub struct _19; impl Value for _19 { const VALUE: u32 = 19; }
/// Type representing the value 20 for the `Value` trait.
pub struct _20; impl Value for _20 { const VALUE: u32 = 20; }
/// Type representing the value 21 for the `Value` trait.
pub struct _21; impl Value for _21 { const VALUE: u32 = 21; }
/// Type representing the value 22 for the `Value` trait.
pub struct _22; impl Value for _22 { const VALUE: u32 = 22; }
/// Type representing the value 23 for the `Value` trait.
pub struct _23; impl Value for _23 { const VALUE: u32 = 23; }
/// Type representing the value 24 for the `Value` trait.
pub struct _24; impl Value for _24 { const VALUE: u32 = 24; }
/// Type representing the value 25 for the `Value` trait.
pub struct _25; impl Value for _25 { const VALUE: u32 = 25; }
/// Type representing the value 26 for the `Value` trait.
pub struct _26; impl Value for _26 { const VALUE: u32 = 26; }
/// Type representing the value 27 for the `Value` trait.
pub struct _27; impl Value for _27 { const VALUE: u32 = 27; }
/// Type representing the value 28 for the `Value` trait.
pub struct _28; impl Value for _28 { const VALUE: u32 = 28; }
/// Type representing the value 29 for the `Value` trait.
pub struct _29; impl Value for _29 { const VALUE: u32 = 29; }
/// Type representing the value 30 for the `Value` trait.
pub struct _30; impl Value for _30 { const VALUE: u32 = 30; }
/// Type representing the value 31 for the `Value` trait.
pub struct _31; impl Value for _31 { const VALUE: u32 = 31; }
/// Type representing the value 32 for the `Value` trait.
pub struct _32; impl Value for _32 { const VALUE: u32 = 32; }
/// Type representing the value 33 for the `Value` trait.
pub struct _33; impl Value for _33 { const VALUE: u32 = 33; }
/// Type representing the value 34 for the `Value` trait.
pub struct _34; impl Value for _34 { const VALUE: u32 = 34; }
/// Type representing the value 35 for the `Value` trait.
pub struct _35; impl Value for _35 { const VALUE: u32 = 35; }
/// Type representing the value 36 for the `Value` trait.
pub struct _36; impl Value for _36 { const VALUE: u32 = 36; }
/// Type representing the value 37 for the `Value` trait.
pub struct _37; impl Value for _37 { const VALUE: u32 = 37; }
/// Type representing the value 38 for the `Value` trait.
pub struct _38; impl Value for _38 { const VALUE: u32 = 38; }
/// Type representing the value 39 for the `Value` trait.
pub struct _39; impl Value for _39 { const VALUE: u32 = 39; }
/// Type representing the value 40 for the `Value` trait.
pub struct _40; impl Value for _40 { const VALUE: u32 = 40; }
/// Type representing the value 41 for the `Value` trait.
pub struct _41; impl Value for _41 { const VALUE: u32 = 41; }
/// Type representing the value 42 for the `Value` trait.
pub struct _42; impl Value for _42 { const VALUE: u32 = 42; }
/// Type representing the value 43 for the `Value` trait.
pub struct _43; impl Value for _43 { const VALUE: u32 = 43; }
/// Type representing the value 44 for the `Value` trait.
pub struct _44; impl Value for _44 { const VALUE: u32 = 44; }
/// Type representing the value 45 for the `Value` trait.
pub struct _45; impl Value for _45 { const VALUE: u32 = 45; }
/// Type representing the value 46 for the `Value` trait.
pub struct _46; impl Value for _46 { const VALUE: u32 = 46; }
/// Type representing the value 47 for the `Value` trait.
pub struct _47; impl Value for _47 { const VALUE: u32 = 47; }
/// Type representing the value 48 for the `Value` trait.
pub struct _48; impl Value for _48 { const VALUE: u32 = 48; }
/// Type representing the value 49 for the `Value` trait.
pub struct _49; impl Value for _49 { const VALUE: u32 = 49; }
/// Type representing the value 50 for the `Value` trait.
pub struct _50; impl Value for _50 { const VALUE: u32 = 50; }
/// Type representing the value 51 for the `Value` trait.
pub struct _51; impl Value for _51 { const VALUE: u32 = 51; }
/// Type representing the value 52 for the `Value` trait.
pub struct _52; impl Value for _52 { const VALUE: u32 = 52; }
/// Type representing the value 53 for the `Value` trait.
pub struct _53; impl Value for _53 { const VALUE: u32 = 53; }
/// Type representing the value 54 for the `Value` trait.
pub struct _54; impl Value for _54 { const VALUE: u32 = 54; }
/// Type representing the value 55 for the `Value` trait.
pub struct _55; impl Value for _55 { const VALUE: u32 = 55; }
/// Type representing the value 56 for the `Value` trait.
pub struct _56; impl Value for _56 { const VALUE: u32 = 56; }
/// Type representing the value 57 for the `Value` trait.
pub struct _57; impl Value for _57 { const VALUE: u32 = 57; }
/// Type representing the value 58 for the `Value` trait.
pub struct _58; impl Value for _58 { const VALUE: u32 = 58; }
/// Type representing the value 59 for the `Value` trait.
pub struct _59; impl Value for _59 { const VALUE: u32 = 59; }
/// Type representing the value 60 for the `Value` trait.
pub struct _60; impl Value for _60 { const VALUE: u32 = 60; }
/// Type representing the value 61 for the `Value` trait.
pub struct _61; impl Value for _61 { const VALUE: u32 = 61; }
/// Type representing the value 62 for the `Value` trait.
pub struct _62; impl Value for _62 { const VALUE: u32 = 62; }
/// Type representing the value 63 for the `Value` trait.
pub struct _63; impl Value for _63 { const VALUE: u32 = 63; }
/// Type representing the value 64 for the `Value` trait.
pub struct _64; impl Value for _64 { const VALUE: u32 = 64; }
/// Type representing the value 65 for the `Value` trait.
pub struct _65; impl Value for _65 { const VALUE: u32 = 65; }
/// Type representing the value 66 for the `Value` trait.
pub struct _66; impl Value for _66 { const VALUE: u32 = 66; }
/// Type representing the value 67 for the `Value` trait.
pub struct _67; impl Value for _67 { const VALUE: u32 = 67; }
/// Type representing the value 68 for the `Value` trait.
pub struct _68; impl Value for _68 { const VALUE: u32 = 68; }
/// Type representing the value 69 for the `Value` trait.
pub struct _69; impl Value for _69 { const VALUE: u32 = 69; }
/// Type representing the value 70 for the `Value` trait.
pub struct _70; impl Value for _70 { const VALUE: u32 = 70; }
/// Type representing the value 71 for the `Value` trait.
pub struct _71; impl Value for _71 { const VALUE: u32 = 71; }
/// Type representing the value 72 for the `Value` trait.
pub struct _72; impl Value for _72 { const VALUE: u32 = 72; }
/// Type representing the value 73 for the `Value` trait.
pub struct _73; impl Value for _73 { const VALUE: u32 = 73; }
/// Type representing the value 74 for the `Value` trait.
pub struct _74; impl Value for _74 { const VALUE: u32 = 74; }
/// Type representing the value 75 for the `Value` trait.
pub struct _75; impl Value for _75 { const VALUE: u32 = 75; }
/// Type representing the value 76 for the `Value` trait.
pub struct _76; impl Value for _76 { const VALUE: u32 = 76; }
/// Type representing the value 77 for the `Value` trait.
pub struct _77; impl Value for _77 { const VALUE: u32 = 77; }
/// Type representing the value 78 for the `Value` trait.
pub struct _78; impl Value for _78 { const VALUE: u32 = 78; }
/// Type representing the value 79 for the `Value` trait.
pub struct _79; impl Value for _79 { const VALUE: u32 = 79; }
/// Type representing the value 80 for the `Value` trait.
pub struct _80; impl Value for _80 { const VALUE: u32 = 80; }
/// Type representing the value 81 for the `Value` trait.
pub struct _81; impl Value for _81 { const VALUE: u32 = 81; }
/// Type representing the value 82 for the `Value` trait.
pub struct _82; impl Value for _82 { const VALUE: u32 = 82; }
/// Type representing the value 83 for the `Value` trait.
pub struct _83; impl Value for _83 { const VALUE: u32 = 83; }
/// Type representing the value 84 for the `Value` trait.
pub struct _84; impl Value for _84 { const VALUE: u32 = 84; }
/// Type representing the value 85 for the `Value` trait.
pub struct _85; impl Value for _85 { const VALUE: u32 = 85; }
/// Type representing the value 86 for the `Value` trait.
pub struct _86; impl Value for _86 { const VALUE: u32 = 86; }
/// Type representing the value 87 for the `Value` trait.
pub struct _87; impl Value for _87 { const VALUE: u32 = 87; }
/// Type representing the value 88 for the `Value` trait.
pub struct _88; impl Value for _88 { const VALUE: u32 = 88; }
/// Type representing the value 89 for the `Value` trait.
pub struct _89; impl Value for _89 { const VALUE: u32 = 89; }
/// Type representing the value 90 for the `Value` trait.
pub struct _90; impl Value for _90 { const VALUE: u32 = 90; }
/// Type representing the value 91 for the `Value` trait.
pub struct _91; impl Value for _91 { const VALUE: u32 = 91; }
/// Type representing the value 92 for the `Value` trait.
pub struct _92; impl Value for _92 { const VALUE: u32 = 92; }
/// Type representing the value 93 for the `Value` trait.
pub struct _93; impl Value for _93 { const VALUE: u32 = 93; }
/// Type representing the value 94 for the `Value` trait.
pub struct _94; impl Value for _94 { const VALUE: u32 = 94; }
/// Type representing the value 95 for the `Value` trait.
pub struct _95; impl Value for _95 { const VALUE: u32 = 95; }
/// Type representing the value 96 for the `Value` trait.
pub struct _96; impl Value for _96 { const VALUE: u32 = 96; }
/// Type representing the value 97 for the `Value` trait.
pub struct _97; impl Value for _97 { const VALUE: u32 = 97; }
/// Type representing the value 98 for the `Value` trait.
pub struct _98; impl Value for _98 { const VALUE: u32 = 98; }
/// Type representing the value 99 for the `Value` trait.
pub struct _99; impl Value for _99 { const VALUE: u32 = 99; }
/// Type representing the value 100 for the `Value` trait.
pub struct _100; impl Value for _100 { const VALUE: u32 = 100; }
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

