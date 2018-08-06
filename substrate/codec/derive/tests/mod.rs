// Copyright 2018 Parity Technologies (UK) Ltd.
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

extern crate substrate_codec as codec;

#[macro_use]
extern crate substrate_codec_derive;

use codec::{Encode, Decode};

#[derive(Debug, PartialEq, Encode, Decode)]
struct Unit;


#[derive(Debug, PartialEq, Encode, Decode)]
struct Indexed(u32, u64);

#[derive(Debug, PartialEq, Encode, Decode)]
struct Struct<A, B, C> {
	pub a: A,
	pub b: B,
	pub c: C,
}

impl <A, B, C> Struct<A, B, C> {
	fn new(a: A, b: B, c: C) -> Self {
		Self { a, b, c }
	}
}

type TestType = Struct<u32, u64, Vec<u8>>;

#[test]
fn should_derive_encode() {
	let v = TestType::new(15, 9, b"Hello world".to_vec());

	v.using_encoded(|ref slice| {
		assert_eq!(slice, &b"\x0f\0\0\0\x09\0\0\0\0\0\0\0\x0b\0\0\0Hello world")
	});
}

#[test]
fn should_derive_decode() {
	let slice = b"\x0f\0\0\0\x09\0\0\0\0\0\0\0\x0b\0\0\0Hello world".to_vec();

	let v = TestType::decode(&mut &*slice);

	assert_eq!(v, Some(TestType::new(15, 9, b"Hello world".to_vec())));
}

#[test]
fn should_work_for_unit() {
	let v = Unit;

	v.using_encoded(|ref slice| {
		assert_eq!(slice, &[]);
	});

	let mut a: &[u8] = &[];
	assert_eq!(Unit::decode(&mut a), Some(Unit));
}

#[test]
fn should_work_for_indexed() {
	let v = Indexed(1, 2);

	v.using_encoded(|ref slice| {
		assert_eq!(slice, &b"\x01\0\0\0\x02\0\0\0\0\0\0\0")
	});

	let mut v: &[u8] = b"\x01\0\0\0\x02\0\0\0\0\0\0\0";
	assert_eq!(Indexed::decode(&mut v), Some(Indexed(1, 2)));
}
