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

use super::*;
use sp_io::{MultiRemovalResults, TestExternalities};
use sp_metadata_ir::{
	PalletStorageMetadataIR, StorageEntryMetadataIR, StorageEntryModifierIR, StorageEntryTypeIR,
	StorageHasherIR,
};
use sp_runtime::{generic, traits::BlakeTwo256, BuildStorage};

pub use self::frame_system::{pallet_prelude::*, Config, Pallet};

mod storage_alias;

#[pallet]
pub mod frame_system {
	#[allow(unused)]
	use super::{frame_system, frame_system::pallet_prelude::*};
	pub use crate::dispatch::RawOrigin;
	use crate::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config: 'static {
		type Block: Parameter + sp_runtime::traits::Block;
		type AccountId;
		type BaseCallFilter: crate::traits::Contains<Self::RuntimeCall>;
		type RuntimeOrigin;
		type RuntimeCall;
		type PalletInfo: crate::traits::PalletInfo;
		type DbWeight: Get<crate::weights::RuntimeDbWeight>;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Required by construct_runtime
		CallFiltered,
	}

	#[pallet::origin]
	pub type Origin<T> = RawOrigin<<T as Config>::AccountId>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {}

	#[pallet::storage]
	pub type Data<T> = StorageMap<_, Twox64Concat, u32, u64, ValueQuery>;

	#[pallet::storage]
	pub type OptionLinkedMap<T> = StorageMap<_, Blake2_128Concat, u32, u32, OptionQuery>;

	#[pallet::storage]
	#[pallet::getter(fn generic_data)]
	pub type GenericData<T: Config> =
		StorageMap<_, Identity, BlockNumberFor<T>, BlockNumberFor<T>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn generic_data2)]
	pub type GenericData2<T: Config> =
		StorageMap<_, Blake2_128Concat, BlockNumberFor<T>, BlockNumberFor<T>, OptionQuery>;

	#[pallet::storage]
	pub type DataDM<T> =
		StorageDoubleMap<_, Twox64Concat, u32, Blake2_128Concat, u32, u64, ValueQuery>;

	#[pallet::storage]
	pub type GenericDataDM<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		BlockNumberFor<T>,
		Identity,
		BlockNumberFor<T>,
		BlockNumberFor<T>,
		ValueQuery,
	>;

	#[pallet::storage]
	pub type GenericData2DM<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		BlockNumberFor<T>,
		Twox64Concat,
		BlockNumberFor<T>,
		BlockNumberFor<T>,
		OptionQuery,
	>;

	#[pallet::storage]
	#[pallet::unbounded]
	pub type AppendableDM<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		u32,
		Blake2_128Concat,
		BlockNumberFor<T>,
		Vec<u32>,
		ValueQuery,
	>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub data: Vec<(u32, u64)>,
		pub test_config: Vec<(u32, u32, u64)>,
		#[serde(skip)]
		pub _config: sp_std::marker::PhantomData<T>,
	}

	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			Self {
				_config: Default::default(),
				data: vec![(15u32, 42u64)],
				test_config: vec![(15u32, 16u32, 42u64)],
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
		fn build(&self) {
			for (k, v) in &self.data {
				<Data<T>>::insert(k, v);
			}
			for (k1, k2, v) in &self.test_config {
				<DataDM<T>>::insert(k1, k2, v);
			}
		}
	}

	pub mod pallet_prelude {
		pub type OriginFor<T> = <T as super::Config>::RuntimeOrigin;

		pub type HeaderFor<T> =
			<<T as super::Config>::Block as sp_runtime::traits::HeaderProvider>::HeaderT;

		pub type BlockNumberFor<T> = <HeaderFor<T> as sp_runtime::traits::Header>::Number;
	}
}

type BlockNumber = u32;
type AccountId = u32;
type Header = generic::Header<BlockNumber, BlakeTwo256>;
type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, RuntimeCall, (), ()>;
type Block = generic::Block<Header, UncheckedExtrinsic>;

crate::construct_runtime!(
	pub enum Runtime
	{
		System: self::frame_system,
	}
);

impl Config for Runtime {
	type Block = Block;
	type AccountId = AccountId;
	type BaseCallFilter = crate::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type PalletInfo = PalletInfo;
	type DbWeight = ();
}

fn new_test_ext() -> TestExternalities {
	RuntimeGenesisConfig::default().build_storage().unwrap().into()
}

trait Sorted {
	fn sorted(self) -> Self;
}

impl<T: Ord> Sorted for Vec<T> {
	fn sorted(mut self) -> Self {
		self.sort();
		self
	}
}

#[test]
fn map_issue_3318() {
	new_test_ext().execute_with(|| {
		type OptionLinkedMap = self::frame_system::OptionLinkedMap<Runtime>;

		OptionLinkedMap::insert(1, 1);
		assert_eq!(OptionLinkedMap::get(1), Some(1));
		OptionLinkedMap::insert(1, 2);
		assert_eq!(OptionLinkedMap::get(1), Some(2));
	});
}

#[test]
fn map_swap_works() {
	new_test_ext().execute_with(|| {
		type OptionLinkedMap = self::frame_system::OptionLinkedMap<Runtime>;

		OptionLinkedMap::insert(0, 0);
		OptionLinkedMap::insert(1, 1);
		OptionLinkedMap::insert(2, 2);
		OptionLinkedMap::insert(3, 3);

		let collect = || OptionLinkedMap::iter().collect::<Vec<_>>().sorted();
		assert_eq!(collect(), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);

		// Two existing
		OptionLinkedMap::swap(1, 2);
		assert_eq!(collect(), vec![(0, 0), (1, 2), (2, 1), (3, 3)]);

		// Back to normal
		OptionLinkedMap::swap(2, 1);
		assert_eq!(collect(), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);

		// Left existing
		OptionLinkedMap::swap(2, 5);
		assert_eq!(collect(), vec![(0, 0), (1, 1), (3, 3), (5, 2)]);

		// Right existing
		OptionLinkedMap::swap(5, 2);
		assert_eq!(collect(), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);
	});
}

#[test]
fn double_map_swap_works() {
	new_test_ext().execute_with(|| {
		type DataDM = self::frame_system::DataDM<Runtime>;

		DataDM::insert(0, 1, 1);
		DataDM::insert(1, 0, 2);
		DataDM::insert(1, 1, 3);

		let get_all = || {
			vec![
				DataDM::get(0, 1),
				DataDM::get(1, 0),
				DataDM::get(1, 1),
				DataDM::get(2, 0),
				DataDM::get(2, 1),
			]
		};
		assert_eq!(get_all(), vec![1, 2, 3, 0, 0]);

		// Two existing
		DataDM::swap(0, 1, 1, 0);
		assert_eq!(get_all(), vec![2, 1, 3, 0, 0]);

		// Left existing
		DataDM::swap(1, 0, 2, 0);
		assert_eq!(get_all(), vec![2, 0, 3, 1, 0]);

		// Right existing
		DataDM::swap(2, 1, 1, 1);
		assert_eq!(get_all(), vec![2, 0, 0, 1, 3]);
	});
}

#[test]
fn map_basic_insert_remove_should_work() {
	new_test_ext().execute_with(|| {
		type Map = self::frame_system::Data<Runtime>;

		// initialized during genesis
		assert_eq!(Map::get(&15u32), 42u64);

		// get / insert / take
		let key = 17u32;
		assert_eq!(Map::get(&key), 0u64);
		Map::insert(key, 4u64);
		assert_eq!(Map::get(&key), 4u64);
		assert_eq!(Map::take(&key), 4u64);
		assert_eq!(Map::get(&key), 0u64);

		// mutate
		Map::mutate(&key, |val| {
			*val = 15;
		});
		assert_eq!(Map::get(&key), 15u64);

		// remove
		Map::remove(&key);
		assert_eq!(Map::get(&key), 0u64);
	});
}

#[test]
fn map_iteration_should_work() {
	new_test_ext().execute_with(|| {
		type Map = self::frame_system::Data<Runtime>;

		assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(15, 42)]);
		// insert / remove
		let key = 17u32;
		Map::insert(key, 4u64);
		assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(15, 42), (key, 4)]);
		assert_eq!(Map::take(&15), 42u64);
		assert_eq!(Map::take(&key), 4u64);
		assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![]);

		// Add couple of more elements
		Map::insert(key, 42u64);
		assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(key, 42)]);
		Map::insert(key + 1, 43u64);
		assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(key, 42), (key + 1, 43)]);

		// mutate
		let key = key + 2;
		Map::mutate(&key, |val| {
			*val = 15;
		});
		assert_eq!(
			Map::iter().collect::<Vec<_>>().sorted(),
			vec![(key - 2, 42), (key - 1, 43), (key, 15)]
		);
		Map::mutate(&key, |val| {
			*val = 17;
		});
		assert_eq!(
			Map::iter().collect::<Vec<_>>().sorted(),
			vec![(key - 2, 42), (key - 1, 43), (key, 17)]
		);

		// remove first
		Map::remove(&key);
		assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(key - 2, 42), (key - 1, 43)]);

		// remove last from the list
		Map::remove(&(key - 2));
		assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(key - 1, 43)]);

		// remove the last element
		Map::remove(&(key - 1));
		assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![]);
	});
}

#[test]
fn double_map_basic_insert_remove_remove_prefix_with_commit_should_work() {
	let key1 = 17u32;
	let key2 = 18u32;
	type DoubleMap = self::frame_system::DataDM<Runtime>;
	let mut e = new_test_ext();
	e.execute_with(|| {
		// initialized during genesis
		assert_eq!(DoubleMap::get(&15u32, &16u32), 42u64);

		// get / insert / take
		assert_eq!(DoubleMap::get(&key1, &key2), 0u64);
		DoubleMap::insert(&key1, &key2, &4u64);
		assert_eq!(DoubleMap::get(&key1, &key2), 4u64);
		assert_eq!(DoubleMap::take(&key1, &key2), 4u64);
		assert_eq!(DoubleMap::get(&key1, &key2), 0u64);

		// mutate
		DoubleMap::mutate(&key1, &key2, |val| *val = 15);
		assert_eq!(DoubleMap::get(&key1, &key2), 15u64);

		// remove
		DoubleMap::remove(&key1, &key2);
		assert_eq!(DoubleMap::get(&key1, &key2), 0u64);

		// remove prefix
		DoubleMap::insert(&key1, &key2, &4u64);
		DoubleMap::insert(&key1, &(key2 + 1), &4u64);
		DoubleMap::insert(&(key1 + 1), &key2, &4u64);
		DoubleMap::insert(&(key1 + 1), &(key2 + 1), &4u64);
	});
	e.commit_all().unwrap();
	e.execute_with(|| {
		assert!(matches!(
			DoubleMap::clear_prefix(&key1, u32::max_value(), None),
			MultiRemovalResults { maybe_cursor: None, backend: 2, unique: 2, loops: 2 }
		));
		assert_eq!(DoubleMap::get(&key1, &key2), 0u64);
		assert_eq!(DoubleMap::get(&key1, &(key2 + 1)), 0u64);
		assert_eq!(DoubleMap::get(&(key1 + 1), &key2), 4u64);
		assert_eq!(DoubleMap::get(&(key1 + 1), &(key2 + 1)), 4u64);
	});
}

#[test]
fn double_map_basic_insert_remove_remove_prefix_should_work() {
	new_test_ext().execute_with(|| {
		let key1 = 17u32;
		let key2 = 18u32;
		type DoubleMap = self::frame_system::DataDM<Runtime>;

		// initialized during genesis
		assert_eq!(DoubleMap::get(&15u32, &16u32), 42u64);

		// get / insert / take
		assert_eq!(DoubleMap::get(&key1, &key2), 0u64);
		DoubleMap::insert(&key1, &key2, &4u64);
		assert_eq!(DoubleMap::get(&key1, &key2), 4u64);
		assert_eq!(DoubleMap::take(&key1, &key2), 4u64);
		assert_eq!(DoubleMap::get(&key1, &key2), 0u64);

		// mutate
		DoubleMap::mutate(&key1, &key2, |val| *val = 15);
		assert_eq!(DoubleMap::get(&key1, &key2), 15u64);

		// remove
		DoubleMap::remove(&key1, &key2);
		assert_eq!(DoubleMap::get(&key1, &key2), 0u64);

		// remove prefix
		DoubleMap::insert(&key1, &key2, &4u64);
		DoubleMap::insert(&key1, &(key2 + 1), &4u64);
		DoubleMap::insert(&(key1 + 1), &key2, &4u64);
		DoubleMap::insert(&(key1 + 1), &(key2 + 1), &4u64);
		// all in overlay
		assert!(matches!(
			DoubleMap::clear_prefix(&key1, u32::max_value(), None),
			MultiRemovalResults { maybe_cursor: None, backend: 0, unique: 0, loops: 0 }
		));
		// Note this is the incorrect answer (for now), since we are using v2 of
		// `clear_prefix`.
		// When we switch to v3, then this will become:
		//   MultiRemovalResults:: { maybe_cursor: None, backend: 0, unique: 2, loops: 2 },
		assert!(matches!(
			DoubleMap::clear_prefix(&key1, u32::max_value(), None),
			MultiRemovalResults { maybe_cursor: None, backend: 0, unique: 0, loops: 0 }
		));
		assert_eq!(DoubleMap::get(&key1, &key2), 0u64);
		assert_eq!(DoubleMap::get(&key1, &(key2 + 1)), 0u64);
		assert_eq!(DoubleMap::get(&(key1 + 1), &key2), 4u64);
		assert_eq!(DoubleMap::get(&(key1 + 1), &(key2 + 1)), 4u64);
	});
}

#[test]
fn double_map_append_should_work() {
	new_test_ext().execute_with(|| {
		type DoubleMap = self::frame_system::AppendableDM<Runtime>;

		let key1 = 17u32;
		let key2 = 18u32;

		DoubleMap::insert(&key1, &key2, &vec![1]);
		DoubleMap::append(&key1, &key2, 2);
		assert_eq!(DoubleMap::get(&key1, &key2), &[1, 2]);
	});
}

#[test]
fn double_map_mutate_exists_should_work() {
	new_test_ext().execute_with(|| {
		type DoubleMap = self::frame_system::DataDM<Runtime>;

		let (key1, key2) = (11, 13);

		// mutated
		DoubleMap::mutate_exists(key1, key2, |v| *v = Some(1));
		assert_eq!(DoubleMap::get(&key1, key2), 1);

		// removed if mutated to `None`
		DoubleMap::mutate_exists(key1, key2, |v| *v = None);
		assert!(!DoubleMap::contains_key(&key1, key2));
	});
}

#[test]
fn double_map_try_mutate_exists_should_work() {
	new_test_ext().execute_with(|| {
		type DoubleMap = self::frame_system::DataDM<Runtime>;
		type TestResult = Result<(), &'static str>;

		let (key1, key2) = (11, 13);

		// mutated if `Ok`
		assert_ok!(DoubleMap::try_mutate_exists(key1, key2, |v| -> TestResult {
			*v = Some(1);
			Ok(())
		}));
		assert_eq!(DoubleMap::get(&key1, key2), 1);

		// no-op if `Err`
		assert_noop!(
			DoubleMap::try_mutate_exists(key1, key2, |v| -> TestResult {
				*v = Some(2);
				Err("nah")
			}),
			"nah"
		);

		// removed if mutated to`None`
		assert_ok!(DoubleMap::try_mutate_exists(key1, key2, |v| -> TestResult {
			*v = None;
			Ok(())
		}));
		assert!(!DoubleMap::contains_key(&key1, key2));
	});
}

fn expected_metadata() -> PalletStorageMetadataIR {
	PalletStorageMetadataIR {
		prefix: "System",
		entries: vec![
			StorageEntryMetadataIR {
				name: "Data",
				modifier: StorageEntryModifierIR::Default,
				ty: StorageEntryTypeIR::Map {
					hashers: vec![StorageHasherIR::Twox64Concat],
					key: scale_info::meta_type::<u32>(),
					value: scale_info::meta_type::<u64>(),
				},
				default: vec![0, 0, 0, 0, 0, 0, 0, 0],
				docs: vec![],
			},
			StorageEntryMetadataIR {
				name: "OptionLinkedMap",
				modifier: StorageEntryModifierIR::Optional,
				ty: StorageEntryTypeIR::Map {
					hashers: vec![StorageHasherIR::Blake2_128Concat],
					key: scale_info::meta_type::<u32>(),
					value: scale_info::meta_type::<u32>(),
				},
				default: vec![0],
				docs: vec![],
			},
			StorageEntryMetadataIR {
				name: "GenericData",
				modifier: StorageEntryModifierIR::Default,
				ty: StorageEntryTypeIR::Map {
					hashers: vec![StorageHasherIR::Identity],
					key: scale_info::meta_type::<u32>(),
					value: scale_info::meta_type::<u32>(),
				},
				default: vec![0, 0, 0, 0],
				docs: vec![],
			},
			StorageEntryMetadataIR {
				name: "GenericData2",
				modifier: StorageEntryModifierIR::Optional,
				ty: StorageEntryTypeIR::Map {
					hashers: vec![StorageHasherIR::Blake2_128Concat],
					key: scale_info::meta_type::<u32>(),
					value: scale_info::meta_type::<u32>(),
				},
				default: vec![0],
				docs: vec![],
			},
			StorageEntryMetadataIR {
				name: "DataDM",
				modifier: StorageEntryModifierIR::Default,
				ty: StorageEntryTypeIR::Map {
					hashers: vec![StorageHasherIR::Twox64Concat, StorageHasherIR::Blake2_128Concat],
					key: scale_info::meta_type::<(u32, u32)>(),
					value: scale_info::meta_type::<u64>(),
				},
				default: vec![0, 0, 0, 0, 0, 0, 0, 0],
				docs: vec![],
			},
			StorageEntryMetadataIR {
				name: "GenericDataDM",
				modifier: StorageEntryModifierIR::Default,
				ty: StorageEntryTypeIR::Map {
					hashers: vec![StorageHasherIR::Blake2_128Concat, StorageHasherIR::Identity],
					key: scale_info::meta_type::<(u32, u32)>(),
					value: scale_info::meta_type::<u32>(),
				},
				default: vec![0, 0, 0, 0],
				docs: vec![],
			},
			StorageEntryMetadataIR {
				name: "GenericData2DM",
				modifier: StorageEntryModifierIR::Optional,
				ty: StorageEntryTypeIR::Map {
					hashers: vec![StorageHasherIR::Blake2_128Concat, StorageHasherIR::Twox64Concat],
					key: scale_info::meta_type::<(u32, u32)>(),
					value: scale_info::meta_type::<u32>(),
				},
				default: vec![0],
				docs: vec![],
			},
			StorageEntryMetadataIR {
				name: "AppendableDM",
				modifier: StorageEntryModifierIR::Default,
				ty: StorageEntryTypeIR::Map {
					hashers: vec![
						StorageHasherIR::Blake2_128Concat,
						StorageHasherIR::Blake2_128Concat,
					],
					key: scale_info::meta_type::<(u32, u32)>(),
					value: scale_info::meta_type::<Vec<u32>>(),
				},
				default: vec![0],
				docs: vec![],
			},
		],
	}
}

#[test]
fn store_metadata() {
	let metadata = Pallet::<Runtime>::storage_metadata();
	pretty_assertions::assert_eq!(expected_metadata(), metadata);
}

parameter_types! {
	storage StorageParameter: u64 = 10;
}

#[test]
fn check_storage_parameter_type_works() {
	TestExternalities::default().execute_with(|| {
		assert_eq!(sp_io::hashing::twox_128(b":StorageParameter:"), StorageParameter::key());

		assert_eq!(10, StorageParameter::get());

		StorageParameter::set(&300);
		assert_eq!(300, StorageParameter::get());
	})
}
