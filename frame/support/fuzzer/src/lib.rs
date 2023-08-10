// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Shared code for fuzzers.

pub use frame_support::{
	metadata_ir::{StorageEntryModifierIR, StorageEntryTypeIR, StorageHasherIR},
	pallet_prelude::NMapKey,
	parameter_types,
	storage::{types::ValueQuery, StorageList as _},
	Blake2_128Concat,
};
use frame_support::{
	pallet_prelude::{StorageList, StoragePagedNMap},
	storage::{types::StoragePagedList, StorageKeyedList},
	traits::StorageInstance,
};
pub use sp_io::{hashing::twox_128, TestExternalities};

pub enum Op {
	Append(Vec<u32>),
	Drain(u8),
}

impl arbitrary::Arbitrary<'_> for Op {
	fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
		if u.arbitrary::<bool>()? {
			Ok(Op::Append(Vec::<u32>::arbitrary(u)?))
		} else {
			Ok(Op::Drain(u.arbitrary::<u8>()?))
		}
	}
}

impl Op {
	pub fn exec_list<List: StorageList<u32>>(self) -> i64 {
		match self {
			Op::Append(v) => {
				let l = v.len();
				List::append_many(v);
				l as i64
			},
			Op::Drain(v) => -(List::drain().take(v as usize).count() as i64),
		}
	}

	pub fn exec_map(self, key: u32) -> i64 {
		match self {
			Op::Append(v) => {
				let l = v.len();
				NMap::append_many((key,), v);
				l as i64
			},
			Op::Drain(v) => -(NMap::drain((key,)).take(v as usize).count() as i64),
		}
	}
}

pub struct KeyedOp {
	pub op: Op,
	pub key: u32,
}

pub enum AllInOneOp {
	List(Op),
	NMap(KeyedOp),
}

impl arbitrary::Arbitrary<'_> for KeyedOp {
	fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
		Ok(KeyedOp { op: Op::arbitrary(u)?, key: u.arbitrary::<u32>()? })
	}
}

impl arbitrary::Arbitrary<'_> for AllInOneOp {
	fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
		if u.arbitrary::<bool>()? {
			Ok(AllInOneOp::List(Op::arbitrary(u)?))
		} else {
			Ok(AllInOneOp::NMap(KeyedOp::arbitrary(u)?))
		}
	}
}

parameter_types! {
	pub storage HeapSize: u32 = 20;
	pub const MaxPages: Option<u32> = Some(20);
}

pub struct Prefix;
impl StorageInstance for Prefix {
	fn pallet_prefix() -> &'static str {
		"test"
	}
	const STORAGE_PREFIX: &'static str = "foo";
}
pub struct Prefix2;
impl StorageInstance for Prefix2 {
	fn pallet_prefix() -> &'static str {
		"test"
	}
	const STORAGE_PREFIX: &'static str = "foo2";
}

pub type List = StoragePagedList<Prefix, u32, HeapSize>;
pub type NMap = StoragePagedNMap<Prefix, (NMapKey<Blake2_128Concat, u32>,), u32, HeapSize>;
