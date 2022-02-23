// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Tests for DebugNoBound, CloneNoBound, EqNoBound, PartialEqNoBound, DefaultNoBound, and
//! RuntimeDebugNoBound

use frame_support::{
	CloneNoBound, DebugNoBound, DefaultNoBound, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};

#[derive(RuntimeDebugNoBound)]
struct Unnamed(u64);

#[test]
fn runtime_debug_no_bound_display_correctly() {
	// This test is not executed without std
	assert_eq!(format!("{:?}", Unnamed(1)), "Unnamed(1)");
}

trait Config {
	type C: std::fmt::Debug + Clone + Eq + PartialEq + Default;
}

struct Runtime;
struct ImplNone;

impl Config for Runtime {
	type C = u32;
}

#[derive(DebugNoBound, CloneNoBound, EqNoBound, PartialEqNoBound, DefaultNoBound)]
struct StructNamed<T: Config, U, V> {
	a: u32,
	b: u64,
	c: T::C,
	phantom: core::marker::PhantomData<(U, V)>,
}

#[test]
fn test_struct_named() {
	let a_1 = StructNamed::<Runtime, ImplNone, ImplNone> {
		a: 1,
		b: 2,
		c: 3,
		phantom: Default::default(),
	};

	let a_default: StructNamed<Runtime, ImplNone, ImplNone> = Default::default();
	assert_eq!(a_default.a, 0);
	assert_eq!(a_default.b, 0);
	assert_eq!(a_default.c, 0);
	assert_eq!(a_default.phantom, Default::default());

	let a_2 = a_1.clone();
	assert_eq!(a_2.a, 1);
	assert_eq!(a_2.b, 2);
	assert_eq!(a_2.c, 3);
	assert_eq!(a_2, a_1);
	assert_eq!(
		format!("{:?}", a_1),
		String::from("StructNamed { a: 1, b: 2, c: 3, phantom: PhantomData }")
	);

	let b = StructNamed::<Runtime, ImplNone, ImplNone> {
		a: 1,
		b: 2,
		c: 4,
		phantom: Default::default(),
	};

	assert!(b != a_1);
}

#[derive(DebugNoBound, CloneNoBound, EqNoBound, PartialEqNoBound, DefaultNoBound)]
struct StructUnnamed<T: Config, U, V>(u32, u64, T::C, core::marker::PhantomData<(U, V)>);

#[test]
fn test_struct_unnamed() {
	let a_1 = StructUnnamed::<Runtime, ImplNone, ImplNone>(1, 2, 3, Default::default());

	let a_default: StructUnnamed<Runtime, ImplNone, ImplNone> = Default::default();
	assert_eq!(a_default.0, 0);
	assert_eq!(a_default.1, 0);
	assert_eq!(a_default.2, 0);
	assert_eq!(a_default.3, Default::default());

	let a_2 = a_1.clone();
	assert_eq!(a_2.0, 1);
	assert_eq!(a_2.1, 2);
	assert_eq!(a_2.2, 3);
	assert_eq!(a_2, a_1);
	assert_eq!(format!("{:?}", a_1), String::from("StructUnnamed(1, 2, 3, PhantomData)"));

	let b = StructUnnamed::<Runtime, ImplNone, ImplNone>(1, 2, 4, Default::default());

	assert!(b != a_1);
}

#[derive(DebugNoBound, CloneNoBound, EqNoBound, PartialEqNoBound, DefaultNoBound)]
enum Enum<T: Config, U, V> {
	VariantUnnamed(u32, u64, T::C, core::marker::PhantomData<(U, V)>),
	VariantNamed { a: u32, b: u64, c: T::C, phantom: core::marker::PhantomData<(U, V)> },
	VariantUnit,
	VariantUnit2,
}

// enum that will have a named default.
#[derive(DebugNoBound, CloneNoBound, EqNoBound, PartialEqNoBound, DefaultNoBound)]
enum Enum2<T: Config> {
	VariantNamed { a: u32, b: u64, c: T::C },
	VariantUnnamed(u32, u64, T::C),
	VariantUnit,
	VariantUnit2,
}

// enum that will have a unit default.
#[derive(DebugNoBound, CloneNoBound, EqNoBound, PartialEqNoBound, DefaultNoBound)]
enum Enum3<T: Config> {
	VariantUnit,
	VariantNamed { a: u32, b: u64, c: T::C },
	VariantUnnamed(u32, u64, T::C),
	VariantUnit2,
}

#[test]
fn test_enum() {
	type TestEnum = Enum<Runtime, ImplNone, ImplNone>;
	let variant_0 = TestEnum::VariantUnnamed(1, 2, 3, Default::default());
	let variant_0_bis = TestEnum::VariantUnnamed(1, 2, 4, Default::default());
	let variant_1 = TestEnum::VariantNamed { a: 1, b: 2, c: 3, phantom: Default::default() };
	let variant_1_bis = TestEnum::VariantNamed { a: 1, b: 2, c: 4, phantom: Default::default() };
	let variant_2 = TestEnum::VariantUnit;
	let variant_3 = TestEnum::VariantUnit2;

	let default: TestEnum = Default::default();
	assert_eq!(
		default,
		// first variant is default.
		TestEnum::VariantUnnamed(0, 0, 0, Default::default())
	);

	assert_eq!(Enum2::<Runtime>::default(), Enum2::<Runtime>::VariantNamed { a: 0, b: 0, c: 0 });
	assert_eq!(Enum3::<Runtime>::default(), Enum3::<Runtime>::VariantUnit);

	assert!(variant_0 != variant_0_bis);
	assert!(variant_1 != variant_1_bis);
	assert!(variant_0 != variant_1);
	assert!(variant_0 != variant_2);
	assert!(variant_0 != variant_3);
	assert!(variant_1 != variant_0);
	assert!(variant_1 != variant_2);
	assert!(variant_1 != variant_3);
	assert!(variant_2 != variant_0);
	assert!(variant_2 != variant_1);
	assert!(variant_2 != variant_3);
	assert!(variant_3 != variant_0);
	assert!(variant_3 != variant_1);
	assert!(variant_3 != variant_2);

	assert!(variant_0.clone() == variant_0);
	assert!(variant_1.clone() == variant_1);
	assert!(variant_2.clone() == variant_2);
	assert!(variant_3.clone() == variant_3);

	assert_eq!(
		format!("{:?}", variant_0),
		String::from("Enum::VariantUnnamed(1, 2, 3, PhantomData)"),
	);
	assert_eq!(
		format!("{:?}", variant_1),
		String::from("Enum::VariantNamed { a: 1, b: 2, c: 3, phantom: PhantomData }"),
	);
	assert_eq!(format!("{:?}", variant_2), String::from("Enum::VariantUnit"));
	assert_eq!(format!("{:?}", variant_3), String::from("Enum::VariantUnit2"));
}
