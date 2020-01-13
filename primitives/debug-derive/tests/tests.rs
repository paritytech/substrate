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

use sp_debug_derive::RuntimeDebug;

#[derive(RuntimeDebug)]
struct Unnamed(u64, String);

#[derive(RuntimeDebug)]
struct Named {
	a: u64,
	b: String,
}

#[derive(RuntimeDebug)]
enum EnumLongName<A> {
	A,
	B(A, String),
	VariantLongName {
		a: A,
		b: String,
	},
}


#[test]
fn should_display_proper_debug() {
	use self::EnumLongName as Enum;

	assert_eq!(
		format!("{:?}", Unnamed(1, "abc".into())),
		"Unnamed(1, \"abc\")"
	);
	assert_eq!(
		format!("{:?}", Named { a: 1, b: "abc".into() }),
		"Named { a: 1, b: \"abc\" }"
	);
	assert_eq!(
		format!("{:?}", Enum::<u64>::A),
		"EnumLongName::A"
	);
	assert_eq!(
		format!("{:?}", Enum::B(1, "abc".into())),
		"EnumLongName::B(1, \"abc\")"
	);
	assert_eq!(
		format!("{:?}", Enum::VariantLongName { a: 1, b: "abc".into() }),
		"EnumLongName::VariantLongName { a: 1, b: \"abc\" }"
	);
}
