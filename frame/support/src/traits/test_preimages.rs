// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Tests for the preimages traits.

#![cfg(test)]

use super::*;
use crate::{bounded_vec, traits::Bounded, BoundedVec};
use sp_io::hashing::blake2_256;

#[test]
fn bounded_basic_works() {
	let data: BoundedVec<u8, _> = bounded_vec![b'a', b'b', b'c'];
	let len = data.len() as u32;
	let hash = blake2_256(&data).into();

	// Inline works
	{
		let bound: Bounded<Vec<u8>> = Bounded::Inline(data.clone());
		assert_eq!(bound.hash(), hash);
		assert_eq!(bound.len(), Some(len));
		assert!(!bound.lookup_needed());
		assert_eq!(bound.lookup_len(), None);
	}
	// Legacy works
	{
		let bound: Bounded<Vec<u8>> = Bounded::Legacy { hash, dummy: Default::default() };
		assert_eq!(bound.hash(), hash);
		assert_eq!(bound.len(), None);
		assert!(bound.lookup_needed());
		assert_eq!(bound.lookup_len(), Some(1_000_000));
	}
	// Lookup works
	{
		let bound: Bounded<Vec<u8>> = Bounded::Lookup { hash, len: data.len() as u32 };
		assert_eq!(bound.hash(), hash);
		assert_eq!(bound.len(), Some(len));
		assert!(bound.lookup_needed());
		assert_eq!(bound.lookup_len(), Some(len));
	}
}

#[test]
fn bounded_transmuting_works() {
	let data: BoundedVec<u8, _> = bounded_vec![b'a', b'b', b'c'];

	// Transmute a `String` into a `&str`.
	let x: Bounded<String> = Bounded::Inline(data.clone());
	let y: Bounded<&str> = x.transmute();
	assert_eq!(y, Bounded::Inline(data));
}
