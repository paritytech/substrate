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

#![recursion_limit = "128"]

use frame_support::{
	inherent::{InherentData, InherentIdentifier, MakeFatalError, ProvideInherent},
	metadata_ir::{
		PalletStorageMetadataIR, StorageEntryMetadataIR, StorageEntryModifierIR,
		StorageEntryTypeIR, StorageHasherIR,
	},
	traits::ConstU32,
};
use sp_core::sr25519;
use sp_runtime::{
	generic,
	traits::{BlakeTwo256, Verify},
	BuildStorage,
};

pub trait Currency {}

// Test for:
// * No default instance
// * Origin, Inherent, Event
#[frame_support::pallet(dev_mode)]
mod module1 {
	use self::frame_system::pallet_prelude::*;
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_support_test as frame_system;

	#[pallet::pallet]
	pub struct Pallet<T, I = ()>(_);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;
		type RuntimeOrigin: From<Origin<Self, I>>;
		type SomeParameter: Get<u32>;
		type GenericType: Parameter + Member + MaybeSerializeDeserialize + Default + MaxEncodedLen;
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		#[pallet::weight(0)]
		pub fn one(origin: OriginFor<T>) -> DispatchResult {
			ensure_root(origin)?;
			Self::deposit_event(Event::AnotherVariant(3));
			Ok(())
		}
	}

	#[pallet::storage]
	#[pallet::getter(fn value)]
	pub type Value<T: Config<I>, I: 'static = ()> = StorageValue<_, T::GenericType, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn map)]
	pub type Map<T: Config<I>, I: 'static = ()> = StorageMap<_, Identity, u32, u64, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config<I>, I: 'static = ()> {
		pub value: <T as Config<I>>::GenericType,
		pub test: <T as frame_system::Config>::BlockNumber,
	}

	impl<T: Config<I>, I: 'static> Default for GenesisConfig<T, I> {
		fn default() -> Self {
			Self { value: Default::default(), test: Default::default() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> GenesisBuild<T, I> for GenesisConfig<T, I>
	where
		T::BlockNumber: std::fmt::Display,
	{
		fn build(&self) {
			<Value<T, I>>::put(self.value.clone());
			println!("{}", self.test);
		}
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// Test
		Test,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		_Phantom(PhantomData<T>),
		AnotherVariant(u32),
	}

	#[pallet::origin]
	#[derive(Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, MaxEncodedLen, TypeInfo)]
	#[scale_info(skip_type_params(I))]
	pub enum Origin<T, I = ()> {
		Members(u32),
		_Phantom(PhantomData<(T, I)>),
	}

	pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"12345678";

	#[pallet::inherent]
	impl<T: Config<I>, I: 'static> ProvideInherent for Pallet<T, I>
	where
		T::BlockNumber: From<u32>,
	{
		type Call = Call<T, I>;
		type Error = MakeFatalError<()>;
		const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

		fn create_inherent(_data: &InherentData) -> Option<Self::Call> {
			unimplemented!();
		}

		fn check_inherent(_: &Self::Call, _: &InherentData) -> Result<(), Self::Error> {
			unimplemented!();
		}

		fn is_inherent(_call: &Self::Call) -> bool {
			unimplemented!();
		}
	}
}

// Test for:
// * default instance
// * use of no_genesis_config_phantom_data
#[frame_support::pallet]
mod module2 {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_support_test as frame_system;

	#[pallet::pallet]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		type Amount: Parameter + MaybeSerializeDeserialize + Default + MaxEncodedLen;
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;
		type RuntimeOrigin: From<Origin<Self, I>>;
	}

	impl<T: Config<I>, I: 'static> Currency for Pallet<T, I> {}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {}

	#[pallet::storage]
	pub type Value<T: Config<I>, I: 'static = ()> = StorageValue<_, T::Amount, ValueQuery>;

	#[pallet::storage]
	pub type Map<T: Config<I>, I: 'static = ()> = StorageMap<_, Identity, u64, u64, ValueQuery>;

	#[pallet::storage]
	pub type DoubleMap<T: Config<I>, I: 'static = ()> =
		StorageDoubleMap<_, Identity, u64, Identity, u64, u64, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config<I>, I: 'static = ()> {
		pub value: T::Amount,
		pub map: Vec<(u64, u64)>,
		pub double_map: Vec<(u64, u64, u64)>,
	}

	impl<T: Config<I>, I: 'static> Default for GenesisConfig<T, I> {
		fn default() -> Self {
			Self {
				value: Default::default(),
				map: Default::default(),
				double_map: Default::default(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> GenesisBuild<T, I> for GenesisConfig<T, I>
	where
		T::BlockNumber: std::fmt::Display,
	{
		fn build(&self) {
			<Value<T, I>>::put(self.value.clone());
			for (k, v) in &self.map {
				<Map<T, I>>::insert(k, v);
			}
			for (k1, k2, v) in &self.double_map {
				<DoubleMap<T, I>>::insert(k1, k2, v);
			}
		}
	}

	#[pallet::event]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		Variant(T::Amount),
	}

	#[pallet::origin]
	#[derive(Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, MaxEncodedLen, TypeInfo)]
	#[scale_info(skip_type_params(I))]
	pub enum Origin<T, I = ()> {
		Members(u32),
		_Phantom(PhantomData<(T, I)>),
	}

	pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"12345678";

	#[pallet::inherent]
	impl<T: Config<I>, I: 'static> ProvideInherent for Pallet<T, I> {
		type Call = Call<T, I>;
		type Error = MakeFatalError<()>;
		const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

		fn create_inherent(_data: &InherentData) -> Option<Self::Call> {
			unimplemented!();
		}

		fn check_inherent(_call: &Self::Call, _data: &InherentData) -> Result<(), Self::Error> {
			unimplemented!();
		}

		fn is_inherent(_call: &Self::Call) -> bool {
			unimplemented!();
		}
	}
}

// Test for:
// * Depends on multiple instances of a module with instances
#[frame_support::pallet]
mod module3 {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_support_test as frame_system;

	#[pallet::pallet]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>:
		frame_system::Config + module2::Config<I> + module2::Config<module2::Instance1>
	{
		type Currency: Currency;
		type Currency2: Currency;
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {}
}

pub type BlockNumber = u32;
pub type Signature = sr25519::Signature;
pub type AccountId = <Signature as Verify>::Signer;
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, RuntimeCall, Signature, ()>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_support_test::{Pallet, Call, Event<T>},
		Module1_1: module1::<Instance1>::{
			Pallet, Call, Storage, Event<T>, Config<T>, Origin<T>, Inherent
		},
		Module1_2: module1::<Instance2>::{
			Pallet, Call, Storage, Event<T>, Config<T>, Origin<T>, Inherent
		},
		Module2: module2::{Pallet, Call, Storage, Event<T>, Config<T>, Origin<T>, Inherent},
		Module2_1: module2::<Instance1>::{
			Pallet, Call, Storage, Event<T>, Config<T>, Origin<T>, Inherent
		},
		Module2_2: module2::<Instance2>::{
			Pallet, Call, Storage, Event<T>, Config<T>, Origin<T>, Inherent
		},
		Module2_3: module2::<Instance3>::{
			Pallet, Call, Storage, Event<T>, Config<T>, Origin<T>, Inherent
		},
		Module3: module3::{Pallet, Call},
	}
);

impl frame_support_test::Config for Runtime {
	type BlockNumber = BlockNumber;
	type AccountId = AccountId;
	type BaseCallFilter = frame_support::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type DbWeight = ();
}

impl module1::Config<module1::Instance1> for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type RuntimeOrigin = RuntimeOrigin;
	type SomeParameter = ConstU32<100>;
	type GenericType = u32;
}
impl module1::Config<module1::Instance2> for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type RuntimeOrigin = RuntimeOrigin;
	type SomeParameter = ConstU32<100>;
	type GenericType = u32;
}
impl module2::Config for Runtime {
	type Amount = u16;
	type RuntimeEvent = RuntimeEvent;
	type RuntimeOrigin = RuntimeOrigin;
}
impl module2::Config<module2::Instance1> for Runtime {
	type Amount = u32;
	type RuntimeEvent = RuntimeEvent;
	type RuntimeOrigin = RuntimeOrigin;
}
impl module2::Config<module2::Instance2> for Runtime {
	type Amount = u32;
	type RuntimeEvent = RuntimeEvent;
	type RuntimeOrigin = RuntimeOrigin;
}
impl module2::Config<module2::Instance3> for Runtime {
	type Amount = u64;
	type RuntimeEvent = RuntimeEvent;
	type RuntimeOrigin = RuntimeOrigin;
}
impl module3::Config for Runtime {
	type Currency = Module2_2;
	type Currency2 = Module2_3;
}

fn new_test_ext() -> sp_io::TestExternalities {
	RuntimeGenesisConfig {
		module_1_1: module1::GenesisConfig { value: 3, test: 2 },
		module_1_2: module1::GenesisConfig { value: 4, test: 5 },
		module_2: module2::GenesisConfig {
			value: 4,
			map: vec![(0, 0)],
			double_map: vec![(0, 0, 0)],
		},
		module_2_1: module2::GenesisConfig {
			value: 4,
			map: vec![(0, 0)],
			double_map: vec![(0, 0, 0)],
		},
		module_2_2: Default::default(),
		module_2_3: Default::default(),
	}
	.build_storage()
	.unwrap()
	.into()
}

#[test]
fn storage_instance_independence() {
	let mut storage = sp_core::storage::Storage {
		top: std::collections::BTreeMap::new(),
		children_default: std::collections::HashMap::new(),
	};
	sp_state_machine::BasicExternalities::execute_with_storage(&mut storage, || {
		module2::Value::<Runtime>::put(0);
		module2::Value::<Runtime, module2::Instance1>::put(0);
		module2::Value::<Runtime, module2::Instance2>::put(0);
		module2::Value::<Runtime, module2::Instance3>::put(0);
		module2::Map::<Runtime>::insert(0, 0);
		module2::Map::<Runtime, module2::Instance1>::insert(0, 0);
		module2::Map::<Runtime, module2::Instance2>::insert(0, 0);
		module2::Map::<Runtime, module2::Instance3>::insert(0, 0);
		module2::DoubleMap::<Runtime>::insert(&0, &0, &0);
		module2::DoubleMap::<Runtime, module2::Instance1>::insert(&0, &0, &0);
		module2::DoubleMap::<Runtime, module2::Instance2>::insert(&0, &0, &0);
		module2::DoubleMap::<Runtime, module2::Instance3>::insert(&0, &0, &0);
	});
	// 12 storage values.
	assert_eq!(storage.top.len(), 12);
}

#[test]
fn storage_with_instance_basic_operation() {
	new_test_ext().execute_with(|| {
		type Value = module2::Value<Runtime, module2::Instance1>;
		type Map = module2::Map<Runtime, module2::Instance1>;
		type DoubleMap = module2::DoubleMap<Runtime, module2::Instance1>;

		assert_eq!(Value::exists(), true);
		assert_eq!(Value::get(), 4);
		Value::put(1);
		assert_eq!(Value::get(), 1);
		assert_eq!(Value::take(), 1);
		assert_eq!(Value::get(), 0);
		Value::mutate(|a| *a = 2);
		assert_eq!(Value::get(), 2);
		Value::kill();
		assert_eq!(Value::exists(), false);
		assert_eq!(Value::get(), 0);

		let key = 1;
		assert_eq!(Map::contains_key(0), true);
		assert_eq!(Map::contains_key(key), false);
		Map::insert(key, 1);
		assert_eq!(Map::get(key), 1);
		assert_eq!(Map::take(key), 1);
		assert_eq!(Map::get(key), 0);
		Map::mutate(key, |a| *a = 2);
		assert_eq!(Map::get(key), 2);
		Map::remove(key);
		assert_eq!(Map::contains_key(key), false);
		assert_eq!(Map::get(key), 0);

		let key1 = 1;
		let key2 = 1;
		assert_eq!(DoubleMap::contains_key(&0, &0), true);
		assert_eq!(DoubleMap::contains_key(&key1, &key2), false);
		DoubleMap::insert(&key1, &key2, &1);
		assert_eq!(DoubleMap::get(&key1, &key2), 1);
		assert_eq!(DoubleMap::take(&key1, &key2), 1);
		assert_eq!(DoubleMap::get(&key1, &key2), 0);
		DoubleMap::mutate(&key1, &key2, |a| *a = 2);
		assert_eq!(DoubleMap::get(&key1, &key2), 2);
		DoubleMap::remove(&key1, &key2);
		assert_eq!(DoubleMap::get(&key1, &key2), 0);
	});
}

fn expected_metadata() -> PalletStorageMetadataIR {
	PalletStorageMetadataIR {
		prefix: "Module2_2",
		entries: vec![
			StorageEntryMetadataIR {
				name: "Value",
				modifier: StorageEntryModifierIR::Default,
				ty: StorageEntryTypeIR::Plain(scale_info::meta_type::<u32>()),
				default: vec![0, 0, 0, 0],
				docs: vec![],
			},
			StorageEntryMetadataIR {
				name: "Map",
				modifier: StorageEntryModifierIR::Default,
				ty: StorageEntryTypeIR::Map {
					hashers: vec![StorageHasherIR::Identity],
					key: scale_info::meta_type::<u64>(),
					value: scale_info::meta_type::<u64>(),
				},
				default: [0u8; 8].to_vec(),
				docs: vec![],
			},
			StorageEntryMetadataIR {
				name: "DoubleMap",
				modifier: StorageEntryModifierIR::Default,
				ty: StorageEntryTypeIR::Map {
					hashers: vec![StorageHasherIR::Identity, StorageHasherIR::Identity],
					key: scale_info::meta_type::<(u64, u64)>(),
					value: scale_info::meta_type::<u64>(),
				},
				default: [0u8; 8].to_vec(),
				docs: vec![],
			},
		],
	}
}

#[test]
fn test_instance_storage_metadata() {
	let metadata = Module2_2::storage_metadata();
	pretty_assertions::assert_eq!(expected_metadata(), metadata);
}
