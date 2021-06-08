// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Tests for MaxEncodedLen derive macro

use frame_support::traits::MaxEncodedLen;
use codec::{Compact, Encode};

// These structs won't even compile if the macro isn't working right.

#[derive(Encode, MaxEncodedLen)]
struct Primitives {
	bool: bool,
	eight: u8,
}

#[test]
fn primitives_max_length() {
	assert_eq!(Primitives::max_encoded_len(), 2);
}

#[derive(Encode, MaxEncodedLen)]
struct Composites {
	fixed_size_array: [u8; 128],
	tuple: (u128, u128),
}

#[test]
fn composites_max_length() {
	assert_eq!(Composites::max_encoded_len(), 128 + 16 + 16);
}

#[derive(Encode, MaxEncodedLen)]
struct Generic<T> {
	one: T,
	two: T,
}

#[test]
fn generic_max_length() {
	assert_eq!(Generic::<u8>::max_encoded_len(), u8::max_encoded_len() * 2);
	assert_eq!(Generic::<u32>::max_encoded_len(), u32::max_encoded_len() * 2);
}

#[derive(Encode, MaxEncodedLen)]
struct TwoGenerics<T, U> {
	t: T,
	u: U,
}

#[test]
fn two_generics_max_length() {
	assert_eq!(
		TwoGenerics::<u8, u16>::max_encoded_len(),
		u8::max_encoded_len() + u16::max_encoded_len()
	);
	assert_eq!(
		TwoGenerics::<Compact<u64>, [u16; 8]>::max_encoded_len(),
		Compact::<u64>::max_encoded_len() + <[u16; 8]>::max_encoded_len()
	);
}

#[derive(Encode, MaxEncodedLen)]
struct UnitStruct;

#[test]
fn unit_struct_max_length() {
	assert_eq!(UnitStruct::max_encoded_len(), 0);
}

#[derive(Encode, MaxEncodedLen)]
struct TupleStruct(u8, u32);

#[test]
fn tuple_struct_max_length() {
	assert_eq!(TupleStruct::max_encoded_len(), u8::max_encoded_len() + u32::max_encoded_len());
}

#[derive(Encode, MaxEncodedLen)]
struct TupleGeneric<T>(T, T);

#[test]
fn tuple_generic_max_length() {
	assert_eq!(TupleGeneric::<u8>::max_encoded_len(), u8::max_encoded_len() * 2);
	assert_eq!(TupleGeneric::<u32>::max_encoded_len(), u32::max_encoded_len() * 2);
}

#[derive(Encode, MaxEncodedLen)]
#[allow(unused)]
enum UnitEnum {
	A,
	B,
}

#[test]
fn unit_enum_max_length() {
	assert_eq!(UnitEnum::max_encoded_len(), 1);
}

#[derive(Encode, MaxEncodedLen)]
#[allow(unused)]
enum TupleEnum {
	A(u32),
	B,
}

#[test]
fn tuple_enum_max_length() {
	assert_eq!(TupleEnum::max_encoded_len(), 1 + u32::max_encoded_len());
}

#[derive(Encode, MaxEncodedLen)]
#[allow(unused)]
enum StructEnum {
	A { sixty_four: u64, one_twenty_eight: u128 },
	B,
}

#[test]
fn struct_enum_max_length() {
	assert_eq!(StructEnum::max_encoded_len(), 1 + u64::max_encoded_len() + u128::max_encoded_len());
}

// ensure that enums take the max of variant length, not the sum
#[derive(Encode, MaxEncodedLen)]
#[allow(unused)]
enum EnumMaxNotSum {
	A(u32),
	B(u32),
}

#[test]
fn enum_max_not_sum_max_length() {
	assert_eq!(EnumMaxNotSum::max_encoded_len(), 1 + u32::max_encoded_len());
}
