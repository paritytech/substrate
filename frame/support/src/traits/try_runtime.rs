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

//! Try-runtime specific traits and types.

use super::StorageInstance;
use crate::{
	storage::types::{
		CountedStorageMapInstance, CountedStorageNMapInstance, Counter, KeyGenerator,
		QueryKindTrait,
	},
	traits::{PartialStorageInfoTrait, StorageInfo},
	StorageHasher,
};
use codec::{Decode, DecodeAll, FullCodec};
use impl_trait_for_tuples::impl_for_tuples;
use sp_arithmetic::traits::AtLeast32BitUnsigned;
use sp_core::Get;
use sp_runtime::TryRuntimeError;
use sp_std::prelude::*;

/// Which state tests to execute.
#[derive(codec::Encode, codec::Decode, Clone, scale_info::TypeInfo)]
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

/// Decode the entire data under the given storage type.
///
/// For values, this is trivial. For all kinds of maps, it should decode all the values associated
/// with all keys existing in the map.
///
/// Tuple implementations are provided and simply decode each type in the tuple, summing up the
/// decoded bytes if `Ok(_)`.
pub trait TryDecodeEntireStorage {
	/// Decode the entire data under the given storage, returning `Ok(bytes_decoded)` if success.
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

/// Decode all the values based on the prefix of `info` to `V`.
///
/// Basically, it decodes and sums up all the values who's key start with `info.prefix`. For values,
/// this would be the value itself. For all sorts of maps, this should be all map items in the
/// absence of key collision.
fn decode_storage_info<V: Decode>(info: StorageInfo) -> Result<usize, &'static str> {
	let mut next_key = info.prefix.clone();
	let mut decoded = 0;

	let decode_key = |key: &[u8]| match sp_io::storage::get(key) {
		None => Ok(0),
		Some(bytes) => {
			let len = bytes.len();
			let _ = <V as DecodeAll>::decode_all(&mut bytes.as_ref()).map_err(|_| {
				log::error!(target: crate::LOG_TARGET, "failed to decoded {:?}", info,);
				"failed to decode value under existing key"
			})?;
			Ok::<usize, &'static str>(len)
		},
	};

	decoded += decode_key(&next_key)?;
	loop {
		match sp_io::storage::next_key(&next_key) {
			Some(key) if key.starts_with(&info.prefix) => {
				decoded += decode_key(&key)?;
				next_key = key;
			},
			_ => break,
		}
	}

	Ok(decoded)
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
		let info = Self::partial_storage_info()
			.first()
			.cloned()
			.expect("Value has only one storage info; qed");
		decode_storage_info::<Value>(info)
	}
}

impl<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues> TryDecodeEntireStorage
	for crate::storage::types::StorageMap<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: StorageInstance,
	Hasher: StorageHasher,
	Key: FullCodec,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn try_decode_entire_state() -> Result<usize, &'static str> {
		let info = Self::partial_storage_info()
			.first()
			.cloned()
			.expect("Map has only one storage info; qed");
		decode_storage_info::<Value>(info)
	}
}

impl<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues> TryDecodeEntireStorage
	for crate::storage::types::CountedStorageMap<
		Prefix,
		Hasher,
		Key,
		Value,
		QueryKind,
		OnEmpty,
		MaxValues,
	> where
	Prefix: CountedStorageMapInstance,
	Hasher: StorageHasher,
	Key: FullCodec,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn try_decode_entire_state() -> Result<usize, &'static str> {
		let (map_info, counter_info) = match &Self::partial_storage_info()[..] {
			[a, b] => (a.clone(), b.clone()),
			_ => panic!("Counted map has two storage info items; qed"),
		};
		let mut decoded = decode_storage_info::<Counter>(counter_info)?;
		decoded += decode_storage_info::<Value>(map_info)?;
		Ok(decoded)
	}
}

impl<Prefix, Hasher1, Key1, Hasher2, Key2, Value, QueryKind, OnEmpty, MaxValues>
	TryDecodeEntireStorage
	for crate::storage::types::StorageDoubleMap<
		Prefix,
		Hasher1,
		Key1,
		Hasher2,
		Key2,
		Value,
		QueryKind,
		OnEmpty,
		MaxValues,
	> where
	Prefix: StorageInstance,
	Hasher1: StorageHasher,
	Key1: FullCodec,
	Hasher2: StorageHasher,
	Key2: FullCodec,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn try_decode_entire_state() -> Result<usize, &'static str> {
		let info = Self::partial_storage_info()
			.first()
			.cloned()
			.expect("Double-map has only one storage info; qed");
		decode_storage_info::<Value>(info)
	}
}

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues> TryDecodeEntireStorage
	for crate::storage::types::StorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: StorageInstance,
	Key: KeyGenerator,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn try_decode_entire_state() -> Result<usize, &'static str> {
		let info = Self::partial_storage_info()
			.first()
			.cloned()
			.expect("N-map has only one storage info; qed");
		decode_storage_info::<Value>(info)
	}
}

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues> TryDecodeEntireStorage
	for crate::storage::types::CountedStorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageNMapInstance,
	Key: KeyGenerator,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn try_decode_entire_state() -> Result<usize, &'static str> {
		let (map_info, counter_info) = match &Self::partial_storage_info()[..] {
			[a, b] => (a.clone(), b.clone()),
			_ => panic!("Counted NMap has two storage info items; qed"),
		};

		let mut decoded = decode_storage_info::<Counter>(counter_info)?;
		decoded += decode_storage_info::<Value>(map_info)?;
		Ok(decoded)
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

/// Select which checks should be run when trying a runtime upgrade upgrade.
#[derive(codec::Encode, codec::Decode, Clone, Debug, Copy, scale_info::TypeInfo)]
pub enum UpgradeCheckSelect {
	/// Run no checks.
	None,
	/// Run the `try_state`, `pre_upgrade` and `post_upgrade` checks.
	All,
	/// Run the `pre_upgrade` and `post_upgrade` checks.
	PreAndPost,
	/// Run the `try_state` checks.
	TryState,
}

impl UpgradeCheckSelect {
	/// Whether the pre- and post-upgrade checks are selected.
	pub fn pre_and_post(&self) -> bool {
		matches!(self, Self::All | Self::PreAndPost)
	}

	/// Whether the try-state checks are selected.
	pub fn try_state(&self) -> bool {
		matches!(self, Self::All | Self::TryState)
	}
}

#[cfg(feature = "std")]
impl core::str::FromStr for UpgradeCheckSelect {
	type Err = &'static str;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		match s.to_lowercase().as_str() {
			"none" => Ok(Self::None),
			"all" => Ok(Self::All),
			"pre-and-post" => Ok(Self::PreAndPost),
			"try-state" => Ok(Self::TryState),
			_ => Err("Invalid CheckSelector"),
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
	fn try_state(_: BlockNumber, _: Select) -> Result<(), TryRuntimeError>;
}

#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(all(feature = "tuples-128"), impl_for_tuples(128))]
impl<BlockNumber: Clone + sp_std::fmt::Debug + AtLeast32BitUnsigned> TryState<BlockNumber>
	for Tuple
{
	for_tuples!( where #( Tuple: crate::traits::PalletInfoAccess )* );
	fn try_state(n: BlockNumber, targets: Select) -> Result<(), TryRuntimeError> {
		match targets {
			Select::None => Ok(()),
			Select::All => {
				let mut result = Ok(());
				for_tuples!( #( result = result.and(Tuple::try_state(n.clone(), targets.clone())); )* );
				result
			},
			Select::RoundRobin(len) => {
				let functions: &[fn(BlockNumber, Select) -> Result<(), TryRuntimeError>] =
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
					fn(BlockNumber, Select) -> Result<(), TryRuntimeError>,
				)] = &[for_tuples!(
					#( (<Tuple as crate::traits::PalletInfoAccess>::name(), Tuple::try_state) ),*
				)];
				let mut result = Ok(());
				pallet_names.iter().for_each(|pallet_name| {
					if let Some((name, try_state_fn)) =
						try_state_fns.iter().find(|(name, _)| name.as_bytes() == pallet_name)
					{
						result = result.and(try_state_fn(n.clone(), targets.clone()));
					} else {
						log::warn!(
							"Pallet {:?} not found",
							sp_std::str::from_utf8(pallet_name).unwrap_or_default()
						);
					}
				});

				result
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		storage::types::{self, Key},
		Blake2_128Concat,
	};

	type H = Blake2_128Concat;

	macro_rules! build_prefix {
		($name:ident) => {
			struct $name;
			impl StorageInstance for $name {
				fn pallet_prefix() -> &'static str {
					"test_pallet"
				}
				const STORAGE_PREFIX: &'static str = stringify!($name);
			}
		};
	}

	build_prefix!(ValuePrefix);
	type Value = types::StorageValue<ValuePrefix, u32>;

	build_prefix!(MapPrefix);
	type Map = types::StorageMap<MapPrefix, H, u32, u32>;

	build_prefix!(CMapCounterPrefix);
	build_prefix!(CMapPrefix);
	impl CountedStorageMapInstance for CMapPrefix {
		type CounterPrefix = CMapCounterPrefix;
	}
	type CMap = types::CountedStorageMap<CMapPrefix, H, u8, u16>;

	build_prefix!(DMapPrefix);
	type DMap = types::StorageDoubleMap<DMapPrefix, H, u32, H, u32, u32>;

	build_prefix!(NMapPrefix);
	type NMap = types::StorageNMap<NMapPrefix, (Key<H, u8>, Key<H, u8>), u128>;

	build_prefix!(CountedNMapCounterPrefix);
	build_prefix!(CountedNMapPrefix);
	impl CountedStorageNMapInstance for CountedNMapPrefix {
		type CounterPrefix = CountedNMapCounterPrefix;
	}
	type CNMap = types::CountedStorageNMap<CountedNMapPrefix, (Key<H, u8>, Key<H, u8>), u128>;

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
		sp_io::TestExternalities::new_empty().execute_with(|| {
			assert_eq!(Map::try_decode_entire_state(), Ok(0));

			Map::insert(0, 42);
			assert_eq!(Map::try_decode_entire_state(), Ok(4));

			Map::insert(0, 42);
			assert_eq!(Map::try_decode_entire_state(), Ok(4));

			Map::insert(1, 42);
			assert_eq!(Map::try_decode_entire_state(), Ok(8));

			Map::remove(0);
			assert_eq!(Map::try_decode_entire_state(), Ok(4));

			// two bytes, cannot be decoded into u32.
			sp_io::storage::set(&Map::hashed_key_for(2), &[0u8, 1]);
			assert!(Map::try_decode_entire_state().is_err());
		})
	}

	#[test]
	fn try_decode_entire_state_counted_map_works() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			// counter is not even initialized;
			assert_eq!(CMap::try_decode_entire_state(), Ok(0 + 0));

			let counter = 4;
			let value_size = std::mem::size_of::<u16>();

			CMap::insert(0, 42);
			assert_eq!(CMap::try_decode_entire_state(), Ok(value_size + counter));

			CMap::insert(0, 42);
			assert_eq!(CMap::try_decode_entire_state(), Ok(value_size + counter));

			CMap::insert(1, 42);
			assert_eq!(CMap::try_decode_entire_state(), Ok(value_size * 2 + counter));

			CMap::remove(0);
			assert_eq!(CMap::try_decode_entire_state(), Ok(value_size + counter));

			// counter is cleared again.
			let _ = CMap::clear(u32::MAX, None);
			assert_eq!(CMap::try_decode_entire_state(), Ok(0 + 0));

			// 1 bytes, cannot be decoded into u16.
			sp_io::storage::set(&CMap::hashed_key_for(2), &[0u8]);
			assert!(CMap::try_decode_entire_state().is_err());
		})
	}

	#[test]
	fn try_decode_entire_state_double_works() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			assert_eq!(DMap::try_decode_entire_state(), Ok(0));

			DMap::insert(0, 0, 42);
			assert_eq!(DMap::try_decode_entire_state(), Ok(4));

			DMap::insert(0, 0, 42);
			assert_eq!(DMap::try_decode_entire_state(), Ok(4));

			DMap::insert(0, 1, 42);
			assert_eq!(DMap::try_decode_entire_state(), Ok(8));

			DMap::insert(1, 0, 42);
			assert_eq!(DMap::try_decode_entire_state(), Ok(12));

			DMap::remove(0, 0);
			assert_eq!(DMap::try_decode_entire_state(), Ok(8));

			// two bytes, cannot be decoded into u32.
			sp_io::storage::set(&DMap::hashed_key_for(1, 1), &[0u8, 1]);
			assert!(DMap::try_decode_entire_state().is_err());
		})
	}

	#[test]
	fn try_decode_entire_state_n_map_works() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			assert_eq!(NMap::try_decode_entire_state(), Ok(0));

			let value_size = std::mem::size_of::<u128>();

			NMap::insert((0u8, 0), 42);
			assert_eq!(NMap::try_decode_entire_state(), Ok(value_size));

			NMap::insert((0, 0), 42);
			assert_eq!(NMap::try_decode_entire_state(), Ok(value_size));

			NMap::insert((0, 1), 42);
			assert_eq!(NMap::try_decode_entire_state(), Ok(value_size * 2));

			NMap::insert((1, 0), 42);
			assert_eq!(NMap::try_decode_entire_state(), Ok(value_size * 3));

			NMap::remove((0, 0));
			assert_eq!(NMap::try_decode_entire_state(), Ok(value_size * 2));

			// two bytes, cannot be decoded into u128.
			sp_io::storage::set(&NMap::hashed_key_for((1, 1)), &[0u8, 1]);
			assert!(NMap::try_decode_entire_state().is_err());
		})
	}

	#[test]
	fn try_decode_entire_state_counted_n_map_works() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			sp_io::TestExternalities::new_empty().execute_with(|| {
				assert_eq!(NMap::try_decode_entire_state(), Ok(0));

				let value_size = std::mem::size_of::<u128>();
				let counter = 4;

				CNMap::insert((0u8, 0), 42);
				assert_eq!(CNMap::try_decode_entire_state(), Ok(value_size + counter));

				CNMap::insert((0, 0), 42);
				assert_eq!(CNMap::try_decode_entire_state(), Ok(value_size + counter));

				CNMap::insert((0, 1), 42);
				assert_eq!(CNMap::try_decode_entire_state(), Ok(value_size * 2 + counter));

				CNMap::insert((1, 0), 42);
				assert_eq!(CNMap::try_decode_entire_state(), Ok(value_size * 3 + counter));

				CNMap::remove((0, 0));
				assert_eq!(CNMap::try_decode_entire_state(), Ok(value_size * 2 + counter));

				// two bytes, cannot be decoded into u128.
				sp_io::storage::set(&CNMap::hashed_key_for((1, 1)), &[0u8, 1]);
				assert!(CNMap::try_decode_entire_state().is_err());
			})
		})
	}

	#[test]
	fn extra_bytes_are_rejected() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			assert_eq!(Map::try_decode_entire_state(), Ok(0));

			// 6bytes, too many to fit in u32, should be rejected.
			sp_io::storage::set(&Map::hashed_key_for(2), &[0u8, 1, 3, 4, 5, 6]);
			assert!(Map::try_decode_entire_state().is_err());
		})
	}

	#[test]
	fn try_decode_entire_state_tuple_of_storage_works() {
		sp_io::TestExternalities::new_empty().execute_with(|| {
			assert_eq!(<(Value, Map) as TryDecodeEntireStorage>::try_decode_entire_state(), Ok(0));

			Value::put(42);
			assert_eq!(<(Value, Map) as TryDecodeEntireStorage>::try_decode_entire_state(), Ok(4));

			Map::insert(0, 42);
			assert_eq!(<(Value, Map) as TryDecodeEntireStorage>::try_decode_entire_state(), Ok(8));
		});
	}
}
