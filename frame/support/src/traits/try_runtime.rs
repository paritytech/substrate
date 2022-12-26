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

//! Try-runtime specific traits and types.

use super::StorageInstance;
use crate::{
	storage::{
		generator::value::StorageValue,
		types::{CountedStorageMapInstance, KeyGenerator, QueryKindTrait},
	},
	StorageHasher,
};
use codec::{Decode, FullCodec};
use impl_trait_for_tuples::impl_for_tuples;
use sp_arithmetic::traits::AtLeast32BitUnsigned;
use sp_core::Get;
use sp_std::prelude::*;

// Which state tests to execute.
#[derive(codec::Encode, codec::Decode, Clone)]
pub enum Select {
	/// None of them.
	None,
	/// All of them.
	All,
	/// Run a fixed number of them in a round robin manner.
	RoundRobin(u32),
	/// Run only pallets who's name matches the given list.
	///
	/// Pallet names are obtained from [`super::PalletInfoAccess`].
	Only(Vec<Vec<u8>>),
}

impl Default for Select {
	fn default() -> Self {
		Select::None
	}
}

use crate::storage::generator::map::StorageMap;

/// Decode the entire values under the given storage type.
///
/// For values, this is trivial. For all kinds of maps, it should decode all the values associated
/// with all keys existing in the map.
pub trait TryDecodeEntireStorage {
	fn try_decode_entire_state() -> Result<usize, &'static str>;
}

#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
impl TryDecodeEntireStorage for Tuple {
	fn try_decode_entire_state() -> Result<usize, &'static str> {
		let mut len = 0usize;
		for_tuples!( #( len = len.saturating_add(Tuple::try_decode_entire_state()?); )* );
		Ok(len)
	}
}

fn decode_key<V: Decode>(key: &[u8]) -> Result<usize, &'static str> {
	match sp_io::storage::get(key) {
		None => Ok(0),
		Some(bytes) => {
			let len = bytes.len();
			let _ = <V as Decode>::decode(&mut bytes.as_ref()).map_err(|_| "TODO")?;
			Ok(len)
		},
	}
}

impl<Prefix, Value, QueryKind, OnEmpty> TryDecodeEntireStorage
	for crate::storage::types::StorageValue<Prefix, Value, QueryKind, OnEmpty>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
{
	fn try_decode_entire_state() -> Result<usize, &'static str> {
		let len = decode_key::<Value>(&Self::hashed_key())?;
		// TODO: it will be easier to long such things if we implement these one by one in the
		// macro, which is more or less then same thing as the blanket implementation.
		log::debug!(
			target: crate::LOG_TARGET,
			"decoded {:?}::{:?}, total of {} bytes",
			Self::module_prefix(),
			Self::storage_prefix(),
			len
		);
		Ok(len)
	}
}

impl<Prefix, Hasher, Key, Value, QueryKind, OnEmpty> TryDecodeEntireStorage
	for crate::storage::types::StorageMap<Prefix, Hasher, Key, Value, QueryKind, OnEmpty>
where
	Prefix: StorageInstance,
	Hasher: StorageHasher,
	Key: FullCodec,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
{
	fn try_decode_entire_state() -> Result<usize, &'static str> {
		let mut next_key = Self::prefix_hash();
		let mut len = 0usize;
		while let Some(key) = sp_io::storage::next_key(&next_key) {
			len += decode_key::<Value>(&key)?;
			next_key = key;
		}

		Ok(len)
	}
}

impl<Prefix, Hasher, Key, Value, QueryKind, OnEmpty> TryDecodeEntireStorage
	for crate::storage::types::CountedStorageMap<Prefix, Hasher, Key, Value, QueryKind, OnEmpty>
where
	Prefix: CountedStorageMapInstance,
	Hasher: StorageHasher,
	Key: FullCodec,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
{
	fn try_decode_entire_state() -> Result<usize, &'static str> {
		// TODO: rather not re-hardcode the u32 here.
		let mut len = decode_key::<u32>(&Self::counter_storage_final_key())?;
		let mut next_key = Self::map_storage_final_prefix();
		while let Some(key) = sp_io::storage::next_key(&next_key) {
			len += decode_key::<Value>(&key)?;
			next_key = key;
		}

		Ok(len)
	}
}

impl<Prefix, Hasher1, Key1, Hasher2, Key2, Value, QueryKind, OnEmpty> TryDecodeEntireStorage
	for crate::storage::types::StorageDoubleMap<
		Prefix,
		Hasher1,
		Key1,
		Hasher2,
		Key2,
		Value,
		QueryKind,
		OnEmpty,
	> where
	Prefix: StorageInstance,
	Hasher1: StorageHasher,
	Key1: FullCodec,
	Hasher2: StorageHasher,
	Key2: FullCodec,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
{
	fn try_decode_entire_state() -> Result<usize, &'static str> {
		todo!();
	}
}

impl<Prefix, Key, Value, QueryKind, OnEmpty> TryDecodeEntireStorage
	for crate::storage::types::StorageNMap<Prefix, Key, Value, QueryKind, OnEmpty>
where
	Prefix: StorageInstance,
	Key: KeyGenerator,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
{
	fn try_decode_entire_state() -> Result<usize, &'static str> {
		todo!();
	}
}

impl sp_std::fmt::Debug for Select {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		match self {
			Select::RoundRobin(x) => write!(f, "RoundRobin({})", x),
			Select::Only(x) => write!(
				f,
				"Only({:?})",
				x.iter()
					.map(|x| sp_std::str::from_utf8(x).unwrap_or("<invalid?>"))
					.collect::<Vec<_>>(),
			),
			Select::All => write!(f, "All"),
			Select::None => write!(f, "None"),
		}
	}
}

#[cfg(feature = "std")]
impl sp_std::str::FromStr for Select {
	type Err = &'static str;
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		match s {
			"all" | "All" => Ok(Select::All),
			"none" | "None" => Ok(Select::None),
			_ =>
				if s.starts_with("rr-") {
					let count = s
						.split_once('-')
						.and_then(|(_, count)| count.parse::<u32>().ok())
						.ok_or("failed to parse count")?;
					Ok(Select::RoundRobin(count))
				} else {
					let pallets = s.split(',').map(|x| x.as_bytes().to_vec()).collect::<Vec<_>>();
					Ok(Select::Only(pallets))
				},
		}
	}
}

/// Execute some checks to ensure the internal state of a pallet is consistent.
///
/// Usually, these checks should check all of the invariants that are expected to be held on all of
/// the storage items of your pallet.
///
/// This hook should not alter any storage.
pub trait TryState<BlockNumber> {
	/// Execute the state checks.
	fn try_state(_: BlockNumber, _: Select) -> Result<(), &'static str>;
}

#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(all(feature = "tuples-128"), impl_for_tuples(128))]
impl<BlockNumber: Clone + sp_std::fmt::Debug + AtLeast32BitUnsigned> TryState<BlockNumber>
	for Tuple
{
	for_tuples!( where #( Tuple: crate::traits::PalletInfoAccess )* );
	fn try_state(n: BlockNumber, targets: Select) -> Result<(), &'static str> {
		match targets {
			Select::None => Ok(()),
			Select::All => {
				let mut result = Ok(());
				for_tuples!( #( result = result.and(Tuple::try_state(n.clone(), targets.clone())); )* );
				result
			},
			Select::RoundRobin(len) => {
				let functions: &[fn(BlockNumber, Select) -> Result<(), &'static str>] =
					&[for_tuples!(#( Tuple::try_state ),*)];
				let skip = n.clone() % (functions.len() as u32).into();
				let skip: u32 =
					skip.try_into().unwrap_or_else(|_| sp_runtime::traits::Bounded::max_value());
				let mut result = Ok(());
				for try_state_fn in functions.iter().cycle().skip(skip as usize).take(len as usize)
				{
					result = result.and(try_state_fn(n.clone(), targets.clone()));
				}
				result
			},
			Select::Only(ref pallet_names) => {
				let try_state_fns: &[(
					&'static str,
					fn(BlockNumber, Select) -> Result<(), &'static str>,
				)] = &[for_tuples!(
					#( (<Tuple as crate::traits::PalletInfoAccess>::name(), Tuple::try_state) ),*
				)];
				let mut result = Ok(());
				for (name, try_state_fn) in try_state_fns {
					if pallet_names.iter().any(|n| n == name.as_bytes()) {
						result = result.and(try_state_fn(n.clone(), targets.clone()));
					}
				}
				result
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::Blake2_128Concat;

	struct Prefix;
	impl StorageInstance for Prefix {
		fn pallet_prefix() -> &'static str {
			"test_pallet"
		}
		const STORAGE_PREFIX: &'static str = "val_prefix";
	}

	type Value = crate::storage::types::StorageValue<Prefix, u32>;
	type Map = crate::storage::types::StorageMap<Prefix, Blake2_128Concat, u32, u32>;

	#[test]
	fn try_decode_entire_state_value_works() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			assert_eq!(Value::try_decode_entire_state(), Ok(0));
			Value::put(42);
			assert_eq!(Value::try_decode_entire_state(), Ok(4));
			Value::kill();
			assert_eq!(Value::try_decode_entire_state(), Ok(0));

			// two bytes, cannot be decoded into u32.
			sp_io::storage::set(&Value::hashed_key(), &[0u8, 1]);
			assert!(Value::try_decode_entire_state().is_err());
		})
	}

	#[test]
	fn try_decode_entire_state_map_works() {
		todo!()
	}

	#[test]
	fn try_decode_entire_state_double_works() {
		todo!()
	}

	#[test]
	fn try_decode_entire_state_nmap_works() {
		todo!()
	}

	#[test]
	fn try_decode_entire_state_counted_map_works() {
		todo!()
	}

	#[test]
	fn try_decode_entire_state_tuple_of_storage_works() {
		assert!(<(Value, Map) as TryDecodeEntireStorage>::try_decode_entire_state().is_ok());
	}
}
