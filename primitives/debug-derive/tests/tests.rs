// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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
	VariantLongName { a: A, b: String },
}

#[test]
fn should_display_proper_debug() {
	use self::EnumLongName as Enum;

	assert_eq!(format!("{:?}", Unnamed(1, "abc".into())), "Unnamed(1, \"abc\")");
	assert_eq!(format!("{:?}", Named { a: 1, b: "abc".into() }), "Named { a: 1, b: \"abc\" }");
	assert_eq!(format!("{:?}", Enum::<u64>::A), "EnumLongName::A");
	assert_eq!(format!("{:?}", Enum::B(1, "abc".into())), "EnumLongName::B(1, \"abc\")");
	assert_eq!(
		format!("{:?}", Enum::VariantLongName { a: 1, b: "abc".into() }),
		"EnumLongName::VariantLongName { a: 1, b: \"abc\" }"
	);
}
