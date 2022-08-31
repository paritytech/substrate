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

use frame_support::{
	dispatch::UnfilteredDispatchable,
	pallet_prelude::ValueQuery,
	storage::unhashed,
	traits::{ConstU32, GetCallName, OnFinalize, OnGenesis, OnInitialize, OnRuntimeUpgrade},
	weights::{DispatchClass, DispatchInfo, GetDispatchInfo, Pays},
};
use sp_io::{
	hashing::{blake2_128, twox_128, twox_64},
	TestExternalities,
};
use sp_runtime::{DispatchError, ModuleError};

#[frame_support::pallet]
pub mod pallet {
	use codec::MaxEncodedLen;
	use frame_support::{pallet_prelude::*, parameter_types, scale_info};
	use frame_system::pallet_prelude::*;
	use sp_std::any::TypeId;

	type BalanceOf<T, I> = <T as Config<I>>::Balance;

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		#[pallet::constant]
		type MyGetParam: Get<u32>;
		type Balance: Parameter + Default + scale_info::StaticTypeInfo;
		type Event: From<Event<Self, I>> + IsType<<Self as frame_system::Config>::Event>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::hooks]
	impl<T: Config<I>, I: 'static> Hooks<BlockNumberFor<T>> for Pallet<T, I> {
		fn on_initialize(_: BlockNumberFor<T>) -> Weight {
			if TypeId::of::<I>() == TypeId::of::<()>() {
				Self::deposit_event(Event::Something(10));
				Weight::from_ref_time(10)
			} else {
				Self::deposit_event(Event::Something(11));
				Weight::from_ref_time(11)
			}
		}
		fn on_finalize(_: BlockNumberFor<T>) {
			if TypeId::of::<I>() == TypeId::of::<()>() {
				Self::deposit_event(Event::Something(20));
			} else {
				Self::deposit_event(Event::Something(21));
			}
		}
		fn on_runtime_upgrade() -> Weight {
			if TypeId::of::<I>() == TypeId::of::<()>() {
				Self::deposit_event(Event::Something(30));
				Weight::from_ref_time(30)
			} else {
				Self::deposit_event(Event::Something(31));
				Weight::from_ref_time(31)
			}
		}
		fn integrity_test() {}
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Doc comment put in metadata
		#[pallet::weight(Weight::from_ref_time(*_foo as u64))]
		pub fn foo(
			origin: OriginFor<T>,
			#[pallet::compact] _foo: u32,
		) -> DispatchResultWithPostInfo {
			let _ = origin;
			Self::deposit_event(Event::Something(3));
			Ok(().into())
		}

		/// Doc comment put in metadata
		#[pallet::weight(1)]
		pub fn foo_storage_layer(
			origin: OriginFor<T>,
			#[pallet::compact] _foo: u32,
		) -> DispatchResultWithPostInfo {
			let _ = origin;
			Ok(().into())
		}
	}

	#[pallet::error]
	#[derive(PartialEq, Eq)]
	pub enum Error<T, I = ()> {
		/// doc comment put into metadata
		InsufficientProposersBalance,
		NonExistentStorageValue,
	}

	#[pallet::event]
	#[pallet::generate_deposit(fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// doc comment put in metadata
		Proposed(<T as frame_system::Config>::AccountId),
		/// doc
		Spending(BalanceOf<T, I>),
		Something(u32),
	}

	#[pallet::storage]
	pub type Value<T, I = ()> = StorageValue<_, u32>;

	#[pallet::storage]
	pub type Map<T, I = ()> = StorageMap<_, Blake2_128Concat, u8, u16>;

	#[pallet::storage]
	pub type Map2<T, I = ()> = StorageMap<_, Twox64Concat, u16, u32>;

	parameter_types! {
		pub const Map3Default<T, I>: Result<u64, Error<T, I>> = Ok(1337);
	}

	#[pallet::storage]
	pub type Map3<T, I = ()> = StorageMap<
		_,
		Blake2_128Concat,
		u32,
		u64,
		ResultQuery<Error<T, I>::NonExistentStorageValue>,
		Map3Default<T, I>,
	>;

	#[pallet::storage]
	pub type DoubleMap<T, I = ()> =
		StorageDoubleMap<_, Blake2_128Concat, u8, Twox64Concat, u16, u32>;

	#[pallet::storage]
	pub type DoubleMap2<T, I = ()> =
		StorageDoubleMap<_, Twox64Concat, u16, Blake2_128Concat, u32, u64>;

	#[pallet::storage]
	pub type DoubleMap3<T, I = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		u32,
		Twox64Concat,
		u64,
		u128,
		ResultQuery<Error<T, I>::NonExistentStorageValue>,
	>;

	#[pallet::storage]
	#[pallet::getter(fn nmap)]
	pub type NMap<T, I = ()> = StorageNMap<_, storage::Key<Blake2_128Concat, u8>, u32>;

	#[pallet::storage]
	#[pallet::getter(fn nmap2)]
	pub type NMap2<T, I = ()> =
		StorageNMap<_, (storage::Key<Twox64Concat, u16>, storage::Key<Blake2_128Concat, u32>), u64>;

	#[pallet::storage]
	#[pallet::getter(fn nmap3)]
	pub type NMap3<T, I = ()> = StorageNMap<
		_,
		(NMapKey<Blake2_128Concat, u8>, NMapKey<Twox64Concat, u16>),
		u128,
		ResultQuery<Error<T, I>::NonExistentStorageValue>,
	>;

	#[pallet::genesis_config]
	#[derive(Default)]
	pub struct GenesisConfig {
		_myfield: u32,
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> GenesisBuild<T, I> for GenesisConfig {
		fn build(&self) {}
	}

	#[pallet::origin]
	#[derive(
		EqNoBound,
		RuntimeDebugNoBound,
		CloneNoBound,
		PartialEqNoBound,
		Encode,
		Decode,
		scale_info::TypeInfo,
		MaxEncodedLen,
	)]
	#[scale_info(skip_type_params(T, I))]
	pub struct Origin<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::validate_unsigned]
	impl<T: Config<I>, I: 'static> ValidateUnsigned for Pallet<T, I> {
		type Call = Call<T, I>;
		fn validate_unsigned(
			_source: TransactionSource,
			_call: &Self::Call,
		) -> TransactionValidity {
			Err(TransactionValidityError::Invalid(InvalidTransaction::Call))
		}
	}

	#[pallet::inherent]
	impl<T: Config<I>, I: 'static> ProvideInherent for Pallet<T, I> {
		type Call = Call<T, I>;
		type Error = InherentError;

		const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

		fn create_inherent(_data: &InherentData) -> Option<Self::Call> {
			unimplemented!();
		}

		fn is_inherent(_call: &Self::Call) -> bool {
			unimplemented!();
		}
	}

	#[derive(codec::Encode, sp_runtime::RuntimeDebug)]
	#[cfg_attr(feature = "std", derive(codec::Decode))]
	pub enum InherentError {}

	impl frame_support::inherent::IsFatalError for InherentError {
		fn is_fatal_error(&self) -> bool {
			unimplemented!();
		}
	}

	pub const INHERENT_IDENTIFIER: frame_support::inherent::InherentIdentifier = *b"testpall";
}

// Test that a instantiable pallet with a generic genesis_config is correctly handled
#[frame_support::pallet]
pub mod pallet2 {
	use frame_support::pallet_prelude::*;

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		type Event: From<Event<Self, I>> + IsType<<Self as frame_system::Config>::Event>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::event]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// Something
		Something(u32),
	}

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config<I>, I: 'static = ()> {
		phantom: PhantomData<(T, I)>,
	}

	impl<T: Config<I>, I: 'static> Default for GenesisConfig<T, I> {
		fn default() -> Self {
			GenesisConfig { phantom: Default::default() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> GenesisBuild<T, I> for GenesisConfig<T, I> {
		fn build(&self) {}
	}
}

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u32;
	type Call = Call;
	type Hash = sp_runtime::testing::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = ConstU32<250>;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}
impl pallet::Config for Runtime {
	type Event = Event;
	type MyGetParam = ConstU32<10>;
	type Balance = u64;
}
impl pallet::Config<pallet::Instance1> for Runtime {
	type Event = Event;
	type MyGetParam = ConstU32<10>;
	type Balance = u64;
}
impl pallet2::Config for Runtime {
	type Event = Event;
}
impl pallet2::Config<pallet::Instance1> for Runtime {
	type Event = Event;
}

pub type Header = sp_runtime::generic::Header<u32, sp_runtime::traits::BlakeTwo256>;
pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, Call, (), ()>;

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		// Exclude part `Storage` in order not to check its metadata in tests.
		System: frame_system exclude_parts { Storage },
		Example: pallet,
		Instance1Example: pallet::<Instance1>,
		Example2: pallet2,
		Instance1Example2: pallet2::<Instance1>,
	}
);

use frame_support::weights::Weight;

#[test]
fn call_expand() {
	let call_foo = pallet::Call::<Runtime>::foo { foo: 3 };
	assert_eq!(
		call_foo.get_dispatch_info(),
		DispatchInfo {
			weight: Weight::from_ref_time(3),
			class: DispatchClass::Normal,
			pays_fee: Pays::Yes
		}
	);
	assert_eq!(call_foo.get_call_name(), "foo");
	assert_eq!(pallet::Call::<Runtime>::get_call_names(), &["foo", "foo_storage_layer"]);

	let call_foo = pallet::Call::<Runtime, pallet::Instance1>::foo { foo: 3 };
	assert_eq!(
		call_foo.get_dispatch_info(),
		DispatchInfo {
			weight: Weight::from_ref_time(3),
			class: DispatchClass::Normal,
			pays_fee: Pays::Yes
		}
	);
	assert_eq!(call_foo.get_call_name(), "foo");
	assert_eq!(
		pallet::Call::<Runtime, pallet::Instance1>::get_call_names(),
		&["foo", "foo_storage_layer"],
	);
}

#[test]
fn error_expand() {
	assert_eq!(
		format!("{:?}", pallet::Error::<Runtime>::InsufficientProposersBalance),
		String::from("InsufficientProposersBalance"),
	);
	assert_eq!(
		<&'static str>::from(pallet::Error::<Runtime>::InsufficientProposersBalance),
		"InsufficientProposersBalance",
	);
	assert_eq!(
		DispatchError::from(pallet::Error::<Runtime>::InsufficientProposersBalance),
		DispatchError::Module(ModuleError {
			index: 1,
			error: [0; 4],
			message: Some("InsufficientProposersBalance")
		}),
	);

	assert_eq!(
		format!("{:?}", pallet::Error::<Runtime, pallet::Instance1>::InsufficientProposersBalance),
		String::from("InsufficientProposersBalance"),
	);
	assert_eq!(
		<&'static str>::from(
			pallet::Error::<Runtime, pallet::Instance1>::InsufficientProposersBalance
		),
		"InsufficientProposersBalance",
	);
	assert_eq!(
		DispatchError::from(
			pallet::Error::<Runtime, pallet::Instance1>::InsufficientProposersBalance
		),
		DispatchError::Module(ModuleError {
			index: 2,
			error: [0; 4],
			message: Some("InsufficientProposersBalance")
		}),
	);
}

#[test]
fn instance_expand() {
	// assert same type
	let _: pallet::__InherentHiddenInstance = ();
}

#[test]
fn pallet_expand_deposit_event() {
	TestExternalities::default().execute_with(|| {
		frame_system::Pallet::<Runtime>::set_block_number(1);
		pallet::Call::<Runtime>::foo { foo: 3 }
			.dispatch_bypass_filter(None.into())
			.unwrap();
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[0].event,
			Event::Example(pallet::Event::Something(3)),
		);
	});

	TestExternalities::default().execute_with(|| {
		frame_system::Pallet::<Runtime>::set_block_number(1);
		pallet::Call::<Runtime, pallet::Instance1>::foo { foo: 3 }
			.dispatch_bypass_filter(None.into())
			.unwrap();
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[0].event,
			Event::Instance1Example(pallet::Event::Something(3)),
		);
	});
}

#[test]
fn storage_expand() {
	use frame_support::{pallet_prelude::*, storage::StoragePrefixedMap};

	fn twox_64_concat(d: &[u8]) -> Vec<u8> {
		let mut v = twox_64(d).to_vec();
		v.extend_from_slice(d);
		v
	}

	fn blake2_128_concat(d: &[u8]) -> Vec<u8> {
		let mut v = blake2_128(d).to_vec();
		v.extend_from_slice(d);
		v
	}

	TestExternalities::default().execute_with(|| {
		<pallet::Value<Runtime>>::put(1);
		let k = [twox_128(b"Example"), twox_128(b"Value")].concat();
		assert_eq!(unhashed::get::<u32>(&k), Some(1u32));

		<pallet::Map<Runtime>>::insert(1, 2);
		let mut k = [twox_128(b"Example"), twox_128(b"Map")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u16>(&k), Some(2u16));
		assert_eq!(&k[..32], &<pallet::Map<Runtime>>::final_prefix());

		<pallet::Map2<Runtime>>::insert(1, 2);
		let mut k = [twox_128(b"Example"), twox_128(b"Map2")].concat();
		k.extend(1u16.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<pallet::Map2<Runtime>>::final_prefix());

		<pallet::Map3<Runtime>>::insert(1, 2);
		let mut k = [twox_128(b"Example"), twox_128(b"Map3")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u64>(&k), Some(2u64));
		assert_eq!(&k[..32], &<pallet::Map3<Runtime>>::final_prefix());
		assert_eq!(<pallet::Map3<Runtime>>::get(2), Ok(1337));

		<pallet::DoubleMap<Runtime>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Example"), twox_128(b"DoubleMap")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		k.extend(2u16.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<pallet::DoubleMap<Runtime>>::final_prefix());

		<pallet::DoubleMap2<Runtime>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Example"), twox_128(b"DoubleMap2")].concat();
		k.extend(1u16.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u64>(&k), Some(3u64));
		assert_eq!(&k[..32], &<pallet::DoubleMap2<Runtime>>::final_prefix());

		<pallet::DoubleMap3<Runtime>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Example"), twox_128(b"DoubleMap3")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		k.extend(2u64.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u128>(&k), Some(3u128));
		assert_eq!(&k[..32], &<pallet::DoubleMap3<Runtime>>::final_prefix());
		assert_eq!(
			<pallet::DoubleMap3<Runtime>>::get(2, 3),
			Err(pallet::Error::<Runtime>::NonExistentStorageValue),
		);

		<pallet::NMap<Runtime>>::insert((&1,), &3);
		let mut k = [twox_128(b"Example"), twox_128(b"NMap")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<pallet::NMap<Runtime>>::final_prefix());

		<pallet::NMap2<Runtime>>::insert((&1, &2), &3);
		let mut k = [twox_128(b"Example"), twox_128(b"NMap2")].concat();
		k.extend(1u16.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u64>(&k), Some(3u64));
		assert_eq!(&k[..32], &<pallet::NMap2<Runtime>>::final_prefix());

		<pallet::NMap3<Runtime>>::insert((&1, &2), &3);
		let mut k = [twox_128(b"Example"), twox_128(b"NMap3")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		k.extend(2u16.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u128>(&k), Some(3u128));
		assert_eq!(&k[..32], &<pallet::NMap3<Runtime>>::final_prefix());
		assert_eq!(
			<pallet::NMap3<Runtime>>::get((2, 3)),
			Err(pallet::Error::<Runtime>::NonExistentStorageValue),
		);
	});

	TestExternalities::default().execute_with(|| {
		<pallet::Value<Runtime, pallet::Instance1>>::put(1);
		let k = [twox_128(b"Instance1Example"), twox_128(b"Value")].concat();
		assert_eq!(unhashed::get::<u32>(&k), Some(1u32));

		<pallet::Map<Runtime, pallet::Instance1>>::insert(1, 2);
		let mut k = [twox_128(b"Instance1Example"), twox_128(b"Map")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u16>(&k), Some(2u16));
		assert_eq!(&k[..32], &<pallet::Map<Runtime, pallet::Instance1>>::final_prefix());

		<pallet::Map2<Runtime, pallet::Instance1>>::insert(1, 2);
		let mut k = [twox_128(b"Instance1Example"), twox_128(b"Map2")].concat();
		k.extend(1u16.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<pallet::Map2<Runtime, pallet::Instance1>>::final_prefix());

		<pallet::Map3<Runtime, pallet::Instance1>>::insert(1, 2);
		let mut k = [twox_128(b"Instance1Example"), twox_128(b"Map3")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u64>(&k), Some(2u64));
		assert_eq!(&k[..32], &<pallet::Map3<Runtime, pallet::Instance1>>::final_prefix());
		assert_eq!(<pallet::Map3<Runtime, pallet::Instance1>>::get(2), Ok(1337));

		<pallet::DoubleMap<Runtime, pallet::Instance1>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Instance1Example"), twox_128(b"DoubleMap")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		k.extend(2u16.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<pallet::DoubleMap<Runtime, pallet::Instance1>>::final_prefix());

		<pallet::DoubleMap2<Runtime, pallet::Instance1>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Instance1Example"), twox_128(b"DoubleMap2")].concat();
		k.extend(1u16.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u64>(&k), Some(3u64));
		assert_eq!(&k[..32], &<pallet::DoubleMap2<Runtime, pallet::Instance1>>::final_prefix());

		<pallet::DoubleMap3<Runtime, pallet::Instance1>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Instance1Example"), twox_128(b"DoubleMap3")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		k.extend(2u64.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u128>(&k), Some(3u128));
		assert_eq!(&k[..32], &<pallet::DoubleMap3<Runtime, pallet::Instance1>>::final_prefix());
		assert_eq!(
			<pallet::DoubleMap3<Runtime, pallet::Instance1>>::get(2, 3),
			Err(pallet::Error::<Runtime, pallet::Instance1>::NonExistentStorageValue),
		);

		<pallet::NMap<Runtime, pallet::Instance1>>::insert((&1,), &3);
		let mut k = [twox_128(b"Instance1Example"), twox_128(b"NMap")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<pallet::NMap<Runtime, pallet::Instance1>>::final_prefix());

		<pallet::NMap2<Runtime, pallet::Instance1>>::insert((&1, &2), &3);
		let mut k = [twox_128(b"Instance1Example"), twox_128(b"NMap2")].concat();
		k.extend(1u16.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u64>(&k), Some(3u64));
		assert_eq!(&k[..32], &<pallet::NMap2<Runtime, pallet::Instance1>>::final_prefix());

		<pallet::NMap3<Runtime, pallet::Instance1>>::insert((&1, &2), &3);
		let mut k = [twox_128(b"Instance1Example"), twox_128(b"NMap3")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		k.extend(2u16.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u128>(&k), Some(3u128));
		assert_eq!(&k[..32], &<pallet::NMap3<Runtime, pallet::Instance1>>::final_prefix());
		assert_eq!(
			<pallet::NMap3<Runtime, pallet::Instance1>>::get((2, 3)),
			Err(pallet::Error::<Runtime, pallet::Instance1>::NonExistentStorageValue),
		);
	});
}

#[test]
fn pallet_metadata_expands() {
	use frame_support::traits::{CrateVersion, PalletInfoData, PalletsInfoAccess};
	let mut infos = AllPalletsWithSystem::infos();
	infos.sort_by_key(|x| x.index);
	assert_eq!(
		infos,
		vec![
			PalletInfoData {
				index: 0,
				name: "System",
				module_name: "frame_system",
				crate_version: CrateVersion { major: 4, minor: 0, patch: 0 },
			},
			PalletInfoData {
				index: 1,
				name: "Example",
				module_name: "pallet",
				crate_version: CrateVersion { major: 3, minor: 0, patch: 0 },
			},
			PalletInfoData {
				index: 2,
				name: "Instance1Example",
				module_name: "pallet",
				crate_version: CrateVersion { major: 3, minor: 0, patch: 0 },
			},
			PalletInfoData {
				index: 3,
				name: "Example2",
				module_name: "pallet2",
				crate_version: CrateVersion { major: 3, minor: 0, patch: 0 },
			},
			PalletInfoData {
				index: 4,
				name: "Instance1Example2",
				module_name: "pallet2",
				crate_version: CrateVersion { major: 3, minor: 0, patch: 0 },
			},
		]
	);
}

#[test]
fn pallet_hooks_expand() {
	TestExternalities::default().execute_with(|| {
		frame_system::Pallet::<Runtime>::set_block_number(1);

		assert_eq!(AllPalletsWithoutSystem::on_initialize(1), Weight::from_ref_time(21));
		AllPalletsWithoutSystem::on_finalize(1);

		assert_eq!(AllPalletsWithoutSystem::on_runtime_upgrade(), Weight::from_ref_time(61));

		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[0].event,
			Event::Example(pallet::Event::Something(10)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[1].event,
			Event::Instance1Example(pallet::Event::Something(11)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[2].event,
			Event::Example(pallet::Event::Something(20)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[3].event,
			Event::Instance1Example(pallet::Event::Something(21)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[4].event,
			Event::Example(pallet::Event::Something(30)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[5].event,
			Event::Instance1Example(pallet::Event::Something(31)),
		);
	})
}

#[test]
fn pallet_on_genesis() {
	TestExternalities::default().execute_with(|| {
		pallet::Pallet::<Runtime>::on_genesis();

		pallet::Pallet::<Runtime, pallet::Instance1>::on_genesis();
	})
}

#[test]
fn metadata() {
	use frame_support::metadata::*;

	let system_pallet_metadata = PalletMetadata {
		index: 0,
		name: "System",
		storage: None, // The storage metadatas have been excluded.
		calls: Some(scale_info::meta_type::<frame_system::Call<Runtime>>().into()),
		event: Some(PalletEventMetadata {
			ty: scale_info::meta_type::<frame_system::Event<Runtime>>(),
		}),
		constants: vec![
			PalletConstantMetadata {
				name: "BlockWeights",
				ty: scale_info::meta_type::<frame_system::limits::BlockWeights>(),
				value: vec![],
				docs: vec![],
			},
			PalletConstantMetadata {
				name: "BlockLength",
				ty: scale_info::meta_type::<frame_system::limits::BlockLength>(),
				value: vec![],
				docs: vec![],
			},
			PalletConstantMetadata {
				name: "BlockHashCount",
				ty: scale_info::meta_type::<u32>(),
				value: vec![],
				docs: vec![],
			},
			PalletConstantMetadata {
				name: "DbWeight",
				ty: scale_info::meta_type::<frame_support::weights::RuntimeDbWeight>(),
				value: vec![],
				docs: vec![],
			},
			PalletConstantMetadata {
				name: "Version",
				ty: scale_info::meta_type::<sp_version::RuntimeVersion>(),
				value: vec![],
				docs: vec![],
			},
			PalletConstantMetadata {
				name: "SS58Prefix",
				ty: scale_info::meta_type::<u16>(),
				value: vec![],
				docs: vec![],
			},
		],
		error: Some(PalletErrorMetadata {
			ty: scale_info::meta_type::<frame_system::Error<Runtime>>(),
		}),
	};

	let example_pallet_metadata = PalletMetadata {
		index: 1,
		name: "Example",
		storage: Some(PalletStorageMetadata {
			prefix: "Example",
			entries: vec![
				StorageEntryMetadata {
					name: "Value",
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Plain(scale_info::meta_type::<u32>()),
					default: vec![0],
					docs: vec![],
				},
				StorageEntryMetadata {
					name: "Map",
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						key: scale_info::meta_type::<u8>(),
						value: scale_info::meta_type::<u16>(),
						hashers: vec![StorageHasher::Blake2_128Concat],
					},
					default: vec![0],
					docs: vec![],
				},
				StorageEntryMetadata {
					name: "Map2",
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						key: scale_info::meta_type::<u16>(),
						value: scale_info::meta_type::<u32>(),
						hashers: vec![StorageHasher::Twox64Concat],
					},
					default: vec![0],
					docs: vec![],
				},
				StorageEntryMetadata {
					name: "Map3",
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						key: scale_info::meta_type::<u32>(),
						value: scale_info::meta_type::<u64>(),
						hashers: vec![StorageHasher::Blake2_128Concat],
					},
					default: vec![0, 57, 5, 0, 0, 0, 0, 0, 0],
					docs: vec![],
				},
				StorageEntryMetadata {
					name: "DoubleMap",
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						value: scale_info::meta_type::<u32>(),
						key: scale_info::meta_type::<(u8, u16)>(),
						hashers: vec![StorageHasher::Blake2_128Concat, StorageHasher::Twox64Concat],
					},
					default: vec![0],
					docs: vec![],
				},
				StorageEntryMetadata {
					name: "DoubleMap2",
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						value: scale_info::meta_type::<u64>(),
						key: scale_info::meta_type::<(u16, u32)>(),
						hashers: vec![StorageHasher::Twox64Concat, StorageHasher::Blake2_128Concat],
					},
					default: vec![0],
					docs: vec![],
				},
				StorageEntryMetadata {
					name: "DoubleMap3",
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						value: scale_info::meta_type::<u128>(),
						key: scale_info::meta_type::<(u32, u64)>(),
						hashers: vec![StorageHasher::Blake2_128Concat, StorageHasher::Twox64Concat],
					},
					default: vec![1, 1],
					docs: vec![],
				},
				StorageEntryMetadata {
					name: "NMap",
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						key: scale_info::meta_type::<u8>(),
						hashers: vec![StorageHasher::Blake2_128Concat],
						value: scale_info::meta_type::<u32>(),
					},
					default: vec![0],
					docs: vec![],
				},
				StorageEntryMetadata {
					name: "NMap2",
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						key: scale_info::meta_type::<(u16, u32)>(),
						hashers: vec![StorageHasher::Twox64Concat, StorageHasher::Blake2_128Concat],
						value: scale_info::meta_type::<u64>(),
					},
					default: vec![0],
					docs: vec![],
				},
				StorageEntryMetadata {
					name: "NMap3",
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						key: scale_info::meta_type::<(u8, u16)>(),
						hashers: vec![StorageHasher::Blake2_128Concat, StorageHasher::Twox64Concat],
						value: scale_info::meta_type::<u128>(),
					},
					default: vec![1, 1],
					docs: vec![],
				},
			],
		}),
		calls: Some(scale_info::meta_type::<pallet::Call<Runtime>>().into()),
		event: Some(PalletEventMetadata { ty: scale_info::meta_type::<pallet::Event<Runtime>>() }),
		constants: vec![PalletConstantMetadata {
			name: "MyGetParam",
			ty: scale_info::meta_type::<u32>(),
			value: vec![10, 0, 0, 0],
			docs: vec![],
		}],
		error: Some(PalletErrorMetadata { ty: scale_info::meta_type::<pallet::Error<Runtime>>() }),
	};

	let mut example_pallet_instance1_metadata = example_pallet_metadata.clone();
	example_pallet_instance1_metadata.name = "Instance1Example";
	example_pallet_instance1_metadata.index = 2;
	match example_pallet_instance1_metadata.calls {
		Some(ref mut calls_meta) => {
			calls_meta.ty = scale_info::meta_type::<pallet::Call<Runtime, pallet::Instance1>>();
		},
		_ => unreachable!(),
	}
	match example_pallet_instance1_metadata.event {
		Some(ref mut event_meta) => {
			event_meta.ty = scale_info::meta_type::<pallet::Event<Runtime, pallet::Instance1>>();
		},
		_ => unreachable!(),
	}
	match example_pallet_instance1_metadata.error {
		Some(ref mut error_meta) => {
			error_meta.ty = scale_info::meta_type::<pallet::Error<Runtime, pallet::Instance1>>();
		},
		_ => unreachable!(),
	}
	match example_pallet_instance1_metadata.storage {
		Some(ref mut storage_meta) => {
			storage_meta.prefix = "Instance1Example";
		},
		_ => unreachable!(),
	}

	let pallets =
		vec![system_pallet_metadata, example_pallet_metadata, example_pallet_instance1_metadata];

	let extrinsic = ExtrinsicMetadata {
		ty: scale_info::meta_type::<UncheckedExtrinsic>(),
		version: 4,
		signed_extensions: vec![SignedExtensionMetadata {
			identifier: "UnitSignedExtension",
			ty: scale_info::meta_type::<()>(),
			additional_signed: scale_info::meta_type::<()>(),
		}],
	};

	let expected_metadata: RuntimeMetadataPrefixed =
		RuntimeMetadataLastVersion::new(pallets, extrinsic, scale_info::meta_type::<Runtime>())
			.into();
	let expected_metadata = match expected_metadata.1 {
		RuntimeMetadata::V14(metadata) => metadata,
		_ => panic!("metadata has been bumped, test needs to be updated"),
	};

	let actual_metadata = match Runtime::metadata().1 {
		RuntimeMetadata::V14(metadata) => metadata,
		_ => panic!("metadata has been bumped, test needs to be updated"),
	};

	pretty_assertions::assert_eq!(actual_metadata.pallets[1], expected_metadata.pallets[1]);
	pretty_assertions::assert_eq!(actual_metadata.pallets[2], expected_metadata.pallets[2]);
}

#[test]
fn test_pallet_info_access() {
	assert_eq!(<System as frame_support::traits::PalletInfoAccess>::name(), "System");
	assert_eq!(<Example as frame_support::traits::PalletInfoAccess>::name(), "Example");
	assert_eq!(
		<Instance1Example as frame_support::traits::PalletInfoAccess>::name(),
		"Instance1Example"
	);
	assert_eq!(<Example2 as frame_support::traits::PalletInfoAccess>::name(), "Example2");
	assert_eq!(
		<Instance1Example2 as frame_support::traits::PalletInfoAccess>::name(),
		"Instance1Example2"
	);

	assert_eq!(<System as frame_support::traits::PalletInfoAccess>::index(), 0);
	assert_eq!(<Example as frame_support::traits::PalletInfoAccess>::index(), 1);
	assert_eq!(<Instance1Example as frame_support::traits::PalletInfoAccess>::index(), 2);
	assert_eq!(<Example2 as frame_support::traits::PalletInfoAccess>::index(), 3);
	assert_eq!(<Instance1Example2 as frame_support::traits::PalletInfoAccess>::index(), 4);
}

#[test]
fn test_storage_alias() {
	#[frame_support::storage_alias]
	type Value<T: pallet::Config<I>, I: 'static> =
		StorageValue<pallet::Pallet<T, I>, u32, ValueQuery>;

	TestExternalities::default().execute_with(|| {
		pallet::Value::<Runtime, pallet::Instance1>::put(10);
		assert_eq!(10, Value::<Runtime, pallet::Instance1>::get());
	})
}
