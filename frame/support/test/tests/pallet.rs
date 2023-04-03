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

use frame_support::{
	assert_ok,
	dispatch::{
		DispatchClass, DispatchInfo, Dispatchable, GetDispatchInfo, Parameter, Pays,
		UnfilteredDispatchable,
	},
	dispatch_context::with_context,
	pallet_prelude::{StorageInfoTrait, ValueQuery},
	storage::unhashed,
	traits::{
		ConstU32, GetCallIndex, GetCallName, GetStorageVersion, OnFinalize, OnGenesis,
		OnInitialize, OnRuntimeUpgrade, PalletError, PalletInfoAccess, StorageVersion,
	},
	weights::{RuntimeDbWeight, Weight},
};
use scale_info::{meta_type, TypeInfo};
use sp_io::{
	hashing::{blake2_128, twox_128, twox_64},
	TestExternalities,
};
use sp_runtime::{DispatchError, ModuleError};

/// Latest stable metadata version used for testing.
const LATEST_METADATA_VERSION: u32 = 14;

pub struct SomeType1;
impl From<SomeType1> for u64 {
	fn from(_t: SomeType1) -> Self {
		0u64
	}
}

pub struct SomeType2;
impl From<SomeType2> for u64 {
	fn from(_t: SomeType2) -> Self {
		100u64
	}
}

pub struct SomeType3;
impl From<SomeType3> for u64 {
	fn from(_t: SomeType3) -> Self {
		0u64
	}
}

pub struct SomeType4;
impl From<SomeType4> for u64 {
	fn from(_t: SomeType4) -> Self {
		0u64
	}
}

pub struct SomeType5;
impl From<SomeType5> for u64 {
	fn from(_t: SomeType5) -> Self {
		0u64
	}
}

pub struct SomeType6;
impl From<SomeType6> for u64 {
	fn from(_t: SomeType6) -> Self {
		0u64
	}
}

pub struct SomeType7;
impl From<SomeType7> for u64 {
	fn from(_t: SomeType7) -> Self {
		0u64
	}
}

pub trait SomeAssociation1 {
	type _1: Parameter + codec::MaxEncodedLen + TypeInfo;
}
impl SomeAssociation1 for u64 {
	type _1 = u64;
}

pub trait SomeAssociation2 {
	type _2: Parameter + codec::MaxEncodedLen + TypeInfo;
}
impl SomeAssociation2 for u64 {
	type _2 = u64;
}

#[frame_support::pallet]
/// Pallet documentation
// Comments should not be included in the pallet documentation
#[pallet_doc("../../README.md")]
#[doc = include_str!("../../README.md")]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use sp_runtime::DispatchResult;

	type BalanceOf<T> = <T as Config>::Balance;

	pub(crate) const STORAGE_VERSION: StorageVersion = StorageVersion::new(10);

	#[pallet::config]
	pub trait Config: frame_system::Config
	where
		<Self as frame_system::Config>::AccountId: From<SomeType1> + SomeAssociation1,
	{
		/// Some comment
		/// Some comment
		#[pallet::constant]
		type MyGetParam: Get<u32>;

		/// Some comment
		/// Some comment
		#[pallet::constant]
		type MyGetParam2: Get<u32>;

		#[pallet::constant]
		type MyGetParam3: Get<<Self::AccountId as SomeAssociation1>::_1>;

		type Balance: Parameter + Default + TypeInfo;

		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::extra_constants]
	impl<T: Config> Pallet<T>
	where
		T::AccountId: From<SomeType1> + SomeAssociation1 + From<SomeType2>,
	{
		/// Some doc
		/// Some doc
		fn some_extra() -> T::AccountId {
			SomeType2.into()
		}

		/// Some doc
		fn some_extra_extra() -> T::AccountId {
			SomeType1.into()
		}

		/// Some doc
		#[pallet::constant_name(SomeExtraRename)]
		fn some_extra_rename() -> T::AccountId {
			SomeType1.into()
		}
	}

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T>
	where
		T::AccountId: From<SomeType2> + From<SomeType1> + SomeAssociation1,
	{
		fn on_initialize(_: BlockNumberFor<T>) -> Weight {
			let _ = T::AccountId::from(SomeType1); // Test for where clause
			let _ = T::AccountId::from(SomeType2); // Test for where clause
			Self::deposit_event(Event::Something(10));
			Weight::from_parts(10, 0)
		}
		fn on_finalize(_: BlockNumberFor<T>) {
			let _ = T::AccountId::from(SomeType1); // Test for where clause
			let _ = T::AccountId::from(SomeType2); // Test for where clause
			Self::deposit_event(Event::Something(20));
		}
		fn on_runtime_upgrade() -> Weight {
			let _ = T::AccountId::from(SomeType1); // Test for where clause
			let _ = T::AccountId::from(SomeType2); // Test for where clause
			Self::deposit_event(Event::Something(30));
			Weight::from_parts(30, 0)
		}
		fn integrity_test() {
			let _ = T::AccountId::from(SomeType1); // Test for where clause
			let _ = T::AccountId::from(SomeType2); // Test for where clause
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		T::AccountId: From<SomeType1> + From<SomeType3> + SomeAssociation1,
	{
		/// Doc comment put in metadata
		#[pallet::call_index(0)]
		#[pallet::weight(Weight::from_parts(*_foo as u64, 0))]
		pub fn foo(
			origin: OriginFor<T>,
			#[pallet::compact] _foo: u32,
			_bar: u32,
		) -> DispatchResultWithPostInfo {
			let _ = T::AccountId::from(SomeType1); // Test for where clause
			let _ = T::AccountId::from(SomeType3); // Test for where clause
			let _ = origin;
			Self::deposit_event(Event::Something(3));
			Ok(().into())
		}

		/// Doc comment put in metadata
		#[pallet::call_index(1)]
		#[pallet::weight({1})]
		pub fn foo_storage_layer(
			_origin: OriginFor<T>,
			#[pallet::compact] foo: u32,
		) -> DispatchResultWithPostInfo {
			Self::deposit_event(Event::Something(0));
			if foo == 0 {
				Err(Error::<T>::InsufficientProposersBalance)?;
			}

			Ok(().into())
		}

		#[pallet::call_index(4)]
		#[pallet::weight({1})]
		pub fn foo_index_out_of_order(_origin: OriginFor<T>) -> DispatchResult {
			Ok(())
		}

		// Test for DispatchResult return type
		#[pallet::call_index(2)]
		#[pallet::weight({1})]
		pub fn foo_no_post_info(_origin: OriginFor<T>) -> DispatchResult {
			Ok(())
		}

		#[pallet::call_index(3)]
		#[pallet::weight({1})]
		pub fn check_for_dispatch_context(_origin: OriginFor<T>) -> DispatchResult {
			with_context::<(), _>(|_| ()).ok_or_else(|| DispatchError::Unavailable)
		}
	}

	#[pallet::error]
	#[derive(PartialEq, Eq)]
	pub enum Error<T> {
		/// doc comment put into metadata
		InsufficientProposersBalance,
		NonExistentStorageValue,
		Code(u8),
		#[codec(skip)]
		Skipped(u128),
		CompactU8(#[codec(compact)] u8),
	}

	#[pallet::event]
	#[pallet::generate_deposit(fn deposit_event)]
	pub enum Event<T: Config>
	where
		T::AccountId: SomeAssociation1 + From<SomeType1>,
	{
		/// doc comment put in metadata
		Proposed(<T as frame_system::Config>::AccountId),
		/// doc
		Spending(BalanceOf<T>),
		Something(u32),
		SomethingElse(<T::AccountId as SomeAssociation1>::_1),
	}

	#[pallet::storage]
	pub type ValueWhereClause<T: Config>
	where
		T::AccountId: SomeAssociation2,
	= StorageValue<_, <T::AccountId as SomeAssociation2>::_2>;

	#[pallet::storage]
	pub type Value<T> = StorageValue<Value = u32>;

	#[pallet::storage]
	#[pallet::storage_prefix = "Value2"]
	pub type RenamedValue<T> = StorageValue<Value = u64>;

	/// Test some doc
	#[pallet::type_value]
	pub fn MyDefault<T: Config>() -> u16
	where
		T::AccountId: From<SomeType7> + From<SomeType1> + SomeAssociation1,
	{
		let _ = T::AccountId::from(SomeType7); // Test where clause works
		4u16
	}

	#[pallet::storage]
	pub type Map<T: Config>
	where
		T::AccountId: From<SomeType7>,
	= StorageMap<_, Blake2_128Concat, u8, u16, ValueQuery, MyDefault<T>>;

	#[pallet::storage]
	pub type Map2<T> =
		StorageMap<Hasher = Twox64Concat, Key = u16, Value = u32, MaxValues = ConstU32<3>>;

	#[pallet::storage]
	pub type Map3<T> =
		StorageMap<_, Blake2_128Concat, u32, u64, ResultQuery<Error<T>::NonExistentStorageValue>>;

	#[pallet::storage]
	pub type DoubleMap<T> = StorageDoubleMap<_, Blake2_128Concat, u8, Twox64Concat, u16, u32>;

	#[pallet::storage]
	pub type DoubleMap2<T> = StorageDoubleMap<
		Hasher1 = Twox64Concat,
		Key1 = u16,
		Hasher2 = Blake2_128Concat,
		Key2 = u32,
		Value = u64,
		MaxValues = ConstU32<5>,
	>;

	#[pallet::storage]
	pub type DoubleMap3<T> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		u32,
		Twox64Concat,
		u64,
		u128,
		ResultQuery<Error<T>::NonExistentStorageValue>,
	>;

	#[pallet::storage]
	#[pallet::getter(fn nmap)]
	pub type NMap<T> = StorageNMap<_, storage::Key<Blake2_128Concat, u8>, u32>;

	#[pallet::storage]
	#[pallet::getter(fn nmap2)]
	pub type NMap2<T> = StorageNMap<
		Key = (NMapKey<Twox64Concat, u16>, NMapKey<Blake2_128Concat, u32>),
		Value = u64,
		MaxValues = ConstU32<11>,
	>;

	#[pallet::storage]
	#[pallet::getter(fn nmap3)]
	pub type NMap3<T> = StorageNMap<
		_,
		(NMapKey<Blake2_128Concat, u8>, NMapKey<Twox64Concat, u16>),
		u128,
		ResultQuery<Error<T>::NonExistentStorageValue>,
	>;

	#[pallet::storage]
	#[pallet::getter(fn conditional_value)]
	#[cfg(feature = "frame-feature-testing")]
	pub type ConditionalValue<T> = StorageValue<_, u32>;

	#[cfg(feature = "frame-feature-testing")]
	#[pallet::storage]
	#[pallet::getter(fn conditional_map)]
	pub type ConditionalMap<T> =
		StorageMap<_, Twox64Concat, u16, u32, OptionQuery, GetDefault, ConstU32<12>>;

	#[cfg(feature = "frame-feature-testing")]
	#[pallet::storage]
	#[pallet::getter(fn conditional_double_map)]
	pub type ConditionalDoubleMap<T> =
		StorageDoubleMap<_, Blake2_128Concat, u8, Twox64Concat, u16, u32>;

	#[cfg(feature = "frame-feature-testing")]
	#[pallet::storage]
	#[pallet::getter(fn conditional_nmap)]
	pub type ConditionalNMap<T> =
		StorageNMap<_, (storage::Key<Blake2_128Concat, u8>, storage::Key<Twox64Concat, u16>), u32>;

	#[pallet::storage]
	#[pallet::storage_prefix = "RenamedCountedMap"]
	#[pallet::getter(fn counted_storage_map)]
	pub type SomeCountedStorageMap<T> =
		CountedStorageMap<Hasher = Twox64Concat, Key = u8, Value = u32>;

	#[pallet::storage]
	#[pallet::unbounded]
	pub type Unbounded<T> = StorageValue<Value = Vec<u8>>;

	#[pallet::genesis_config]
	#[derive(Default)]
	pub struct GenesisConfig {
		_myfield: u32,
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig
	where
		T::AccountId: From<SomeType1> + SomeAssociation1 + From<SomeType4>,
	{
		fn build(&self) {
			let _ = T::AccountId::from(SomeType1); // Test for where clause
			let _ = T::AccountId::from(SomeType4); // Test for where clause
		}
	}

	#[pallet::origin]
	#[derive(
		EqNoBound,
		RuntimeDebugNoBound,
		CloneNoBound,
		PartialEqNoBound,
		Encode,
		Decode,
		TypeInfo,
		MaxEncodedLen,
	)]
	pub struct Origin<T>(PhantomData<T>);

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T>
	where
		T::AccountId: From<SomeType1> + SomeAssociation1 + From<SomeType5> + From<SomeType3>,
	{
		type Call = Call<T>;
		fn validate_unsigned(_source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			let _ = T::AccountId::from(SomeType1); // Test for where clause
			let _ = T::AccountId::from(SomeType5); // Test for where clause
			if matches!(call, Call::foo_storage_layer { .. }) {
				return Ok(ValidTransaction::default())
			}
			Err(TransactionValidityError::Invalid(InvalidTransaction::Call))
		}
	}

	#[pallet::inherent]
	impl<T: Config> ProvideInherent for Pallet<T>
	where
		T::AccountId: From<SomeType1> + SomeAssociation1 + From<SomeType6> + From<SomeType3>,
	{
		type Call = Call<T>;
		type Error = InherentError;

		const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

		fn create_inherent(_data: &InherentData) -> Option<Self::Call> {
			let _ = T::AccountId::from(SomeType1); // Test for where clause
			let _ = T::AccountId::from(SomeType6); // Test for where clause
			Some(Call::foo_no_post_info {})
		}

		fn is_inherent(call: &Self::Call) -> bool {
			matches!(call, Call::foo_no_post_info {} | Call::foo { .. })
		}

		fn check_inherent(call: &Self::Call, _: &InherentData) -> Result<(), Self::Error> {
			match call {
				Call::foo_no_post_info {} => Ok(()),
				Call::foo { foo: 0, bar: 0 } => Err(InherentError::Fatal),
				Call::foo { .. } => Ok(()),
				_ => unreachable!("other calls are not inherents"),
			}
		}

		fn is_inherent_required(d: &InherentData) -> Result<Option<Self::Error>, Self::Error> {
			match d.get_data::<bool>(b"required") {
				Ok(Some(true)) => Ok(Some(InherentError::Fatal)),
				Ok(Some(false)) | Ok(None) => Ok(None),
				Err(_) => unreachable!("should not happen in tests"),
			}
		}
	}

	#[derive(codec::Encode, sp_runtime::RuntimeDebug)]
	#[cfg_attr(feature = "std", derive(codec::Decode))]
	pub enum InherentError {
		Fatal,
	}

	impl frame_support::inherent::IsFatalError for InherentError {
		fn is_fatal_error(&self) -> bool {
			matches!(self, InherentError::Fatal)
		}
	}

	pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"testpall";
}

// Test that a pallet with non generic event and generic genesis_config is correctly handled
// and that a pallet with the attribute without_storage_info is correctly handled.
#[frame_support::pallet]
pub mod pallet2 {
	use super::{SomeAssociation1, SomeType1};
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config
	where
		<Self as frame_system::Config>::AccountId: From<SomeType1> + SomeAssociation1,
	{
		type RuntimeEvent: From<Event> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::pallet]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T>
	where
		T::AccountId: From<SomeType1> + SomeAssociation1,
	{
		fn on_initialize(_: BlockNumberFor<T>) -> Weight {
			Self::deposit_event(Event::Something(11));
			Weight::zero()
		}
		fn on_finalize(_: BlockNumberFor<T>) {
			Self::deposit_event(Event::Something(21));
		}
		fn on_runtime_upgrade() -> Weight {
			Self::deposit_event(Event::Something(31));
			Weight::zero()
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> where T::AccountId: From<SomeType1> + SomeAssociation1 {}

	#[pallet::storage]
	pub type SomeValue<T: Config> = StorageValue<_, Vec<u32>>;

	#[pallet::storage]
	pub type SomeCountedStorageMap<T> =
		CountedStorageMap<Hasher = Twox64Concat, Key = u8, Value = u32>;

	#[pallet::event]
	#[pallet::generate_deposit(fn deposit_event)]
	pub enum Event {
		/// Something
		Something(u32),
	}

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config>
	where
		T::AccountId: From<SomeType1> + SomeAssociation1,
	{
		phantom: PhantomData<T>,
	}

	impl<T: Config> Default for GenesisConfig<T>
	where
		T::AccountId: From<SomeType1> + SomeAssociation1,
	{
		fn default() -> Self {
			GenesisConfig { phantom: Default::default() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T>
	where
		T::AccountId: From<SomeType1> + SomeAssociation1,
	{
		fn build(&self) {}
	}
}

/// Test that the supertrait check works when we pass some parameter to the `frame_system::Config`.
#[frame_support::pallet]
pub mod pallet3 {
	#[pallet::config]
	pub trait Config:
		frame_system::Config<RuntimeOrigin = <Self as Config>::RuntimeOrigin>
	{
		type RuntimeOrigin;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);
}

#[frame_support::pallet]
pub mod pallet4 {
	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::call]
	impl<T: Config> Pallet<T> {}
}

/// Test that the supertrait check works when we pass some parameter to the `frame_system::Config`.
#[frame_support::pallet]
pub mod pallet5 {
	#[pallet::config]
	pub trait Config:
		frame_system::Config<RuntimeOrigin = <Self as Config>::RuntimeOrigin>
	{
		type RuntimeOrigin;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);
}

frame_support::parameter_types!(
	pub const MyGetParam3: u32 = 12;
);

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u32;
	type RuntimeCall = RuntimeCall;
	type Hash = sp_runtime::testing::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
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
	type RuntimeEvent = RuntimeEvent;
	type MyGetParam = ConstU32<10>;
	type MyGetParam2 = ConstU32<11>;
	type MyGetParam3 = MyGetParam3;
	type Balance = u64;
}

impl pallet2::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
}

impl pallet4::Config for Runtime {}

#[cfg(feature = "frame-feature-testing")]
impl pallet3::Config for Runtime {
	type RuntimeOrigin = RuntimeOrigin;
}

#[cfg(feature = "frame-feature-testing-2")]
impl pallet5::Config for Runtime {
	type RuntimeOrigin = RuntimeOrigin;
}

pub type Header = sp_runtime::generic::Header<u32, sp_runtime::traits::BlakeTwo256>;
pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, RuntimeCall, (), ()>;

frame_support::construct_runtime!(
	pub struct Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		// Exclude part `Storage` in order not to check its metadata in tests.
		System: frame_system exclude_parts { Pallet, Storage },
		Example: pallet,
		Example2: pallet2 exclude_parts { Call },
		#[cfg(feature = "frame-feature-testing")]
		Example3: pallet3,
		Example4: pallet4 use_parts { Call },

		#[cfg(feature = "frame-feature-testing-2")]
		Example5: pallet5,
	}
);

// Test that the part `RuntimeCall` is excluded from Example2 and included in Example4.
fn _ensure_call_is_correctly_excluded_and_included(call: RuntimeCall) {
	match call {
		RuntimeCall::System(_) | RuntimeCall::Example(_) | RuntimeCall::Example4(_) => (),
	}
}

#[test]
fn transactional_works() {
	TestExternalities::default().execute_with(|| {
		frame_system::Pallet::<Runtime>::set_block_number(1);

		pallet::Call::<Runtime>::foo_storage_layer { foo: 0 }
			.dispatch_bypass_filter(None.into())
			.err()
			.unwrap();
		assert!(frame_system::Pallet::<Runtime>::events().is_empty());

		pallet::Call::<Runtime>::foo_storage_layer { foo: 1 }
			.dispatch_bypass_filter(None.into())
			.unwrap();
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()
				.iter()
				.map(|e| &e.event)
				.collect::<Vec<_>>(),
			vec![&RuntimeEvent::Example(pallet::Event::Something(0))],
		);
	})
}

#[test]
fn call_expand() {
	let call_foo = pallet::Call::<Runtime>::foo { foo: 3, bar: 0 };
	assert_eq!(
		call_foo.get_dispatch_info(),
		DispatchInfo {
			weight: frame_support::weights::Weight::from_parts(3, 0),
			class: DispatchClass::Normal,
			pays_fee: Pays::Yes
		}
	);
	assert_eq!(call_foo.get_call_name(), "foo");
	assert_eq!(
		pallet::Call::<Runtime>::get_call_names(),
		&[
			"foo",
			"foo_storage_layer",
			"foo_index_out_of_order",
			"foo_no_post_info",
			"check_for_dispatch_context"
		],
	);

	assert_eq!(call_foo.get_call_index(), 0u8);
	assert_eq!(pallet::Call::<Runtime>::get_call_indices(), &[0u8, 1u8, 4u8, 2u8, 3u8])
}

#[test]
fn call_expand_index() {
	let call_foo = pallet::Call::<Runtime>::foo_index_out_of_order {};

	assert_eq!(call_foo.get_call_index(), 4u8);
	assert_eq!(pallet::Call::<Runtime>::get_call_indices(), &[0u8, 1u8, 4u8, 2u8, 3u8])
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
			error: [0, 0, 0, 0],
			message: Some("InsufficientProposersBalance")
		}),
	);
	assert_eq!(<pallet::Error::<Runtime> as PalletError>::MAX_ENCODED_SIZE, 3);
}

#[test]
fn instance_expand() {
	// Assert same type.
	let _: pallet::__InherentHiddenInstance = ();
}

#[test]
fn inherent_expand() {
	use frame_support::{
		inherent::{BlockT, InherentData},
		traits::EnsureInherentsAreFirst,
	};
	use sp_core::Hasher;
	use sp_runtime::{
		traits::{BlakeTwo256, Header},
		Digest,
	};

	let inherents = InherentData::new().create_extrinsics();

	let expected = vec![UncheckedExtrinsic {
		function: RuntimeCall::Example(pallet::Call::foo_no_post_info {}),
		signature: None,
	}];
	assert_eq!(expected, inherents);

	let block = Block::new(
		Header::new(
			1,
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			Digest::default(),
		),
		vec![
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo_no_post_info {}),
				signature: None,
			},
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo { foo: 1, bar: 0 }),
				signature: None,
			},
		],
	);

	assert!(InherentData::new().check_extrinsics(&block).ok());

	let block = Block::new(
		Header::new(
			1,
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			Digest::default(),
		),
		vec![
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo_no_post_info {}),
				signature: None,
			},
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo { foo: 0, bar: 0 }),
				signature: None,
			},
		],
	);

	assert!(InherentData::new().check_extrinsics(&block).fatal_error());

	let block = Block::new(
		Header::new(
			1,
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			Digest::default(),
		),
		vec![UncheckedExtrinsic {
			function: RuntimeCall::Example(pallet::Call::foo_storage_layer { foo: 0 }),
			signature: None,
		}],
	);

	let mut inherent = InherentData::new();
	inherent.put_data(*b"required", &true).unwrap();
	assert!(inherent.check_extrinsics(&block).fatal_error());

	let block = Block::new(
		Header::new(
			1,
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			Digest::default(),
		),
		vec![UncheckedExtrinsic {
			function: RuntimeCall::Example(pallet::Call::foo_no_post_info {}),
			signature: Some((1, (), ())),
		}],
	);

	let mut inherent = InherentData::new();
	inherent.put_data(*b"required", &true).unwrap();
	assert!(inherent.check_extrinsics(&block).fatal_error());

	let block = Block::new(
		Header::new(
			1,
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			Digest::default(),
		),
		vec![
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo { foo: 1, bar: 1 }),
				signature: None,
			},
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo_storage_layer { foo: 0 }),
				signature: None,
			},
		],
	);

	assert!(Runtime::ensure_inherents_are_first(&block).is_ok());

	let block = Block::new(
		Header::new(
			1,
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			Digest::default(),
		),
		vec![
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo { foo: 1, bar: 1 }),
				signature: None,
			},
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo_storage_layer { foo: 0 }),
				signature: None,
			},
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo_no_post_info {}),
				signature: None,
			},
		],
	);

	assert_eq!(Runtime::ensure_inherents_are_first(&block).err().unwrap(), 2);

	let block = Block::new(
		Header::new(
			1,
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			BlakeTwo256::hash(b"test"),
			Digest::default(),
		),
		vec![
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo { foo: 1, bar: 1 }),
				signature: None,
			},
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo { foo: 1, bar: 0 }),
				signature: Some((1, (), ())),
			},
			UncheckedExtrinsic {
				function: RuntimeCall::Example(pallet::Call::foo_no_post_info {}),
				signature: None,
			},
		],
	);

	assert_eq!(Runtime::ensure_inherents_are_first(&block).err().unwrap(), 2);
}

#[test]
fn validate_unsigned_expand() {
	use frame_support::pallet_prelude::{
		InvalidTransaction, TransactionSource, TransactionValidityError, ValidTransaction,
		ValidateUnsigned,
	};
	let call = pallet::Call::<Runtime>::foo_no_post_info {};

	let validity = pallet::Pallet::validate_unsigned(TransactionSource::Local, &call).unwrap_err();
	assert_eq!(validity, TransactionValidityError::Invalid(InvalidTransaction::Call));

	let call = pallet::Call::<Runtime>::foo_storage_layer { foo: 0 };

	let validity = pallet::Pallet::validate_unsigned(TransactionSource::External, &call).unwrap();
	assert_eq!(validity, ValidTransaction::default());
}

#[test]
fn pallet_expand_deposit_event() {
	TestExternalities::default().execute_with(|| {
		frame_system::Pallet::<Runtime>::set_block_number(1);
		pallet::Call::<Runtime>::foo { foo: 3, bar: 0 }
			.dispatch_bypass_filter(None.into())
			.unwrap();
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[0].event,
			RuntimeEvent::Example(pallet::Event::Something(3)),
		);
	})
}

#[test]
fn pallet_new_call_variant() {
	pallet::Call::<Runtime>::new_call_variant_foo(3, 4);
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
		pallet::Value::<Runtime>::put(1);
		let k = [twox_128(b"Example"), twox_128(b"Value")].concat();
		assert_eq!(unhashed::get::<u32>(&k), Some(1u32));

		pallet::RenamedValue::<Runtime>::put(2);
		let k = [twox_128(b"Example"), twox_128(b"Value2")].concat();
		assert_eq!(unhashed::get::<u64>(&k), Some(2));

		pallet::Map::<Runtime>::insert(1, 2);
		let mut k = [twox_128(b"Example"), twox_128(b"Map")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u16>(&k), Some(2u16));
		assert_eq!(&k[..32], &<pallet::Map<Runtime>>::final_prefix());

		pallet::Map2::<Runtime>::insert(1, 2);
		let mut k = [twox_128(b"Example"), twox_128(b"Map2")].concat();
		k.extend(1u16.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<pallet::Map2<Runtime>>::final_prefix());

		pallet::Map3::<Runtime>::insert(1, 2);
		let mut k = [twox_128(b"Example"), twox_128(b"Map3")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u64>(&k), Some(2u64));
		assert_eq!(&k[..32], &<pallet::Map3<Runtime>>::final_prefix());
		assert_eq!(
			pallet::Map3::<Runtime>::get(2),
			Err(pallet::Error::<Runtime>::NonExistentStorageValue),
		);

		pallet::DoubleMap::<Runtime>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Example"), twox_128(b"DoubleMap")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		k.extend(2u16.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<pallet::DoubleMap<Runtime>>::final_prefix());

		pallet::DoubleMap2::<Runtime>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Example"), twox_128(b"DoubleMap2")].concat();
		k.extend(1u16.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u64>(&k), Some(3u64));
		assert_eq!(&k[..32], &<pallet::DoubleMap2<Runtime>>::final_prefix());

		pallet::DoubleMap3::<Runtime>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Example"), twox_128(b"DoubleMap3")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		k.extend(2u64.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u128>(&k), Some(3u128));
		assert_eq!(&k[..32], &<pallet::DoubleMap3<Runtime>>::final_prefix());
		assert_eq!(
			pallet::DoubleMap3::<Runtime>::get(2, 3),
			Err(pallet::Error::<Runtime>::NonExistentStorageValue),
		);

		pallet::NMap::<Runtime>::insert((&1,), &3);
		let mut k = [twox_128(b"Example"), twox_128(b"NMap")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<pallet::NMap<Runtime>>::final_prefix());

		pallet::NMap2::<Runtime>::insert((&1, &2), &3);
		let mut k = [twox_128(b"Example"), twox_128(b"NMap2")].concat();
		k.extend(1u16.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u64>(&k), Some(3u64));
		assert_eq!(&k[..32], &<pallet::NMap2<Runtime>>::final_prefix());

		pallet::NMap3::<Runtime>::insert((&1, &2), &3);
		let mut k = [twox_128(b"Example"), twox_128(b"NMap3")].concat();
		k.extend(1u8.using_encoded(blake2_128_concat));
		k.extend(2u16.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u128>(&k), Some(3u128));
		assert_eq!(&k[..32], &<pallet::NMap3<Runtime>>::final_prefix());
		assert_eq!(
			pallet::NMap3::<Runtime>::get((2, 3)),
			Err(pallet::Error::<Runtime>::NonExistentStorageValue),
		);

		#[cfg(feature = "frame-feature-testing")]
		{
			pallet::ConditionalValue::<Runtime>::put(1);
			pallet::ConditionalMap::<Runtime>::insert(1, 2);
			pallet::ConditionalDoubleMap::<Runtime>::insert(1, 2, 3);
			pallet::ConditionalNMap::<Runtime>::insert((1, 2), 3);
		}

		pallet::SomeCountedStorageMap::<Runtime>::insert(1, 2);
		let mut k = [twox_128(b"Example"), twox_128(b"RenamedCountedMap")].concat();
		k.extend(1u8.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		let k = [twox_128(b"Example"), twox_128(b"CounterForRenamedCountedMap")].concat();
		assert_eq!(unhashed::get::<u32>(&k), Some(1u32));

		pallet::Unbounded::<Runtime>::put(vec![1, 2]);
		let k = [twox_128(b"Example"), twox_128(b"Unbounded")].concat();
		assert_eq!(unhashed::get::<Vec<u8>>(&k), Some(vec![1, 2]));
	})
}

#[test]
fn pallet_hooks_expand() {
	TestExternalities::default().execute_with(|| {
		frame_system::Pallet::<Runtime>::set_block_number(1);

		assert_eq!(AllPalletsWithoutSystem::on_initialize(1), Weight::from_parts(10, 0));
		AllPalletsWithoutSystem::on_finalize(1);

		assert_eq!(AllPalletsWithoutSystem::on_runtime_upgrade(), Weight::from_parts(30, 0));

		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[0].event,
			RuntimeEvent::Example(pallet::Event::Something(10)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[1].event,
			RuntimeEvent::Example2(pallet2::Event::Something(11)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[2].event,
			RuntimeEvent::Example(pallet::Event::Something(20)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[3].event,
			RuntimeEvent::Example2(pallet2::Event::Something(21)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[4].event,
			RuntimeEvent::Example(pallet::Event::Something(30)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[5].event,
			RuntimeEvent::Example2(pallet2::Event::Something(31)),
		);
	})
}

#[test]
fn all_pallets_type_reversed_order_is_correct() {
	TestExternalities::default().execute_with(|| {
		frame_system::Pallet::<Runtime>::set_block_number(1);

		#[allow(deprecated)]
		{
			assert_eq!(
				AllPalletsWithoutSystemReversed::on_initialize(1),
				Weight::from_parts(10, 0)
			);
			AllPalletsWithoutSystemReversed::on_finalize(1);

			assert_eq!(
				AllPalletsWithoutSystemReversed::on_runtime_upgrade(),
				Weight::from_parts(30, 0)
			);
		}

		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[0].event,
			RuntimeEvent::Example2(pallet2::Event::Something(11)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[1].event,
			RuntimeEvent::Example(pallet::Event::Something(10)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[2].event,
			RuntimeEvent::Example2(pallet2::Event::Something(21)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[3].event,
			RuntimeEvent::Example(pallet::Event::Something(20)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[4].event,
			RuntimeEvent::Example2(pallet2::Event::Something(31)),
		);
		assert_eq!(
			frame_system::Pallet::<Runtime>::events()[5].event,
			RuntimeEvent::Example(pallet::Event::Something(30)),
		);
	})
}

#[test]
fn pallet_on_genesis() {
	TestExternalities::default().execute_with(|| {
		assert_eq!(pallet::Pallet::<Runtime>::on_chain_storage_version(), StorageVersion::new(0));
		pallet::Pallet::<Runtime>::on_genesis();
		assert_eq!(
			pallet::Pallet::<Runtime>::current_storage_version(),
			pallet::Pallet::<Runtime>::on_chain_storage_version(),
		);
	})
}

#[test]
fn migrate_from_pallet_version_to_storage_version() {
	const PALLET_VERSION_STORAGE_KEY_POSTFIX: &[u8] = b":__PALLET_VERSION__:";

	fn pallet_version_key(name: &str) -> [u8; 32] {
		frame_support::storage::storage_prefix(name.as_bytes(), PALLET_VERSION_STORAGE_KEY_POSTFIX)
	}

	TestExternalities::default().execute_with(|| {
		// Insert some fake pallet versions
		sp_io::storage::set(&pallet_version_key(Example::name()), &[1, 2, 3]);
		sp_io::storage::set(&pallet_version_key(Example2::name()), &[1, 2, 3]);
		sp_io::storage::set(&pallet_version_key(System::name()), &[1, 2, 3]);

		// Check that everyone currently is at version 0
		assert_eq!(Example::on_chain_storage_version(), StorageVersion::new(0));
		assert_eq!(Example2::on_chain_storage_version(), StorageVersion::new(0));
		assert_eq!(System::on_chain_storage_version(), StorageVersion::new(0));

		let db_weight = RuntimeDbWeight { read: 0, write: 5 };
		let weight = frame_support::migrations::migrate_from_pallet_version_to_storage_version::<
			AllPalletsWithSystem,
		>(&db_weight);

		let mut pallet_num = 4;
		if cfg!(feature = "frame-feature-testing") {
			pallet_num += 1;
		};
		if cfg!(feature = "frame-feature-testing-2") {
			pallet_num += 1;
		};

		// `pallet_num` pallets, 2 writes and every write costs 5 weight.
		assert_eq!(Weight::from_parts(pallet_num * 2 * 5, 0), weight);

		// All pallet versions should be removed
		assert!(sp_io::storage::get(&pallet_version_key(Example::name())).is_none());
		assert!(sp_io::storage::get(&pallet_version_key(Example2::name())).is_none());
		assert!(sp_io::storage::get(&pallet_version_key(System::name())).is_none());

		assert_eq!(Example::on_chain_storage_version(), pallet::STORAGE_VERSION);
		assert_eq!(Example2::on_chain_storage_version(), StorageVersion::new(0));
		assert_eq!(System::on_chain_storage_version(), StorageVersion::new(0));
	});
}

#[test]
fn metadata() {
	use frame_support::metadata::*;

	fn maybe_docs(doc: Vec<&'static str>) -> Vec<&'static str> {
		if cfg!(feature = "no-metadata-docs") {
			vec![]
		} else {
			doc
		}
	}

	let pallets = vec![
		PalletMetadata {
			index: 1,
			name: "Example",
			storage: Some(PalletStorageMetadata {
				prefix: "Example",
				entries: vec![
					StorageEntryMetadata {
						name: "ValueWhereClause",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Plain(meta_type::<u64>()),
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "Value",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Plain(meta_type::<u32>()),
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "Value2",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Plain(meta_type::<u64>()),
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "Map",
						modifier: StorageEntryModifier::Default,
						ty: StorageEntryType::Map {
							key: meta_type::<u8>(),
							value: meta_type::<u16>(),
							hashers: vec![StorageHasher::Blake2_128Concat],
						},
						default: vec![4, 0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "Map2",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							key: meta_type::<u16>(),
							value: meta_type::<u32>(),
							hashers: vec![StorageHasher::Twox64Concat],
						},
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "Map3",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							key: meta_type::<u32>(),
							value: meta_type::<u64>(),
							hashers: vec![StorageHasher::Blake2_128Concat],
						},
						default: vec![1, 1],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "DoubleMap",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							value: meta_type::<u32>(),
							hashers: vec![
								StorageHasher::Blake2_128Concat,
								StorageHasher::Twox64Concat,
							],
							key: meta_type::<(u8, u16)>(),
						},
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "DoubleMap2",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							value: meta_type::<u64>(),
							key: meta_type::<(u16, u32)>(),
							hashers: vec![
								StorageHasher::Twox64Concat,
								StorageHasher::Blake2_128Concat,
							],
						},
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "DoubleMap3",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							value: meta_type::<u128>(),
							key: meta_type::<(u32, u64)>(),
							hashers: vec![
								StorageHasher::Blake2_128Concat,
								StorageHasher::Twox64Concat,
							],
						},
						default: vec![1, 1],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "NMap",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							key: meta_type::<u8>(),
							hashers: vec![StorageHasher::Blake2_128Concat],
							value: meta_type::<u32>(),
						},
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "NMap2",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							key: meta_type::<(u16, u32)>(),
							hashers: vec![
								StorageHasher::Twox64Concat,
								StorageHasher::Blake2_128Concat,
							],
							value: meta_type::<u64>(),
						},
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "NMap3",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							key: meta_type::<(u8, u16)>(),
							hashers: vec![
								StorageHasher::Blake2_128Concat,
								StorageHasher::Twox64Concat,
							],
							value: meta_type::<u128>(),
						},
						default: vec![1, 1],
						docs: vec![],
					},
					#[cfg(feature = "frame-feature-testing")]
					StorageEntryMetadata {
						name: "ConditionalValue",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Plain(meta_type::<u32>()),
						default: vec![0],
						docs: vec![],
					},
					#[cfg(feature = "frame-feature-testing")]
					StorageEntryMetadata {
						name: "ConditionalMap",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							key: meta_type::<u16>(),
							value: meta_type::<u32>(),
							hashers: vec![StorageHasher::Twox64Concat],
						},
						default: vec![0],
						docs: vec![],
					},
					#[cfg(feature = "frame-feature-testing")]
					StorageEntryMetadata {
						name: "ConditionalDoubleMap",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							value: meta_type::<u32>(),
							key: meta_type::<(u8, u16)>(),
							hashers: vec![
								StorageHasher::Blake2_128Concat,
								StorageHasher::Twox64Concat,
							],
						},
						default: vec![0],
						docs: vec![],
					},
					#[cfg(feature = "frame-feature-testing")]
					StorageEntryMetadata {
						name: "ConditionalNMap",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							key: meta_type::<(u8, u16)>(),
							hashers: vec![
								StorageHasher::Blake2_128Concat,
								StorageHasher::Twox64Concat,
							],
							value: meta_type::<u32>(),
						},
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "RenamedCountedMap",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							hashers: vec![StorageHasher::Twox64Concat],
							key: meta_type::<u8>(),
							value: meta_type::<u32>(),
						},
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "CounterForRenamedCountedMap",
						modifier: StorageEntryModifier::Default,
						ty: StorageEntryType::Plain(meta_type::<u32>()),
						default: vec![0, 0, 0, 0],
						docs: maybe_docs(vec!["Counter for the related counted storage map"]),
					},
					StorageEntryMetadata {
						name: "Unbounded",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Plain(meta_type::<Vec<u8>>()),
						default: vec![0],
						docs: vec![],
					},
				],
			}),
			calls: Some(meta_type::<pallet::Call<Runtime>>().into()),
			event: Some(meta_type::<pallet::Event<Runtime>>().into()),
			constants: vec![
				PalletConstantMetadata {
					name: "MyGetParam",
					ty: meta_type::<u32>(),
					value: vec![10, 0, 0, 0],
					docs: maybe_docs(vec![" Some comment", " Some comment"]),
				},
				PalletConstantMetadata {
					name: "MyGetParam2",
					ty: meta_type::<u32>(),
					value: vec![11, 0, 0, 0],
					docs: maybe_docs(vec![" Some comment", " Some comment"]),
				},
				PalletConstantMetadata {
					name: "MyGetParam3",
					ty: meta_type::<u64>(),
					value: vec![12, 0, 0, 0, 0, 0, 0, 0],
					docs: vec![],
				},
				PalletConstantMetadata {
					name: "some_extra",
					ty: meta_type::<u64>(),
					value: vec![100, 0, 0, 0, 0, 0, 0, 0],
					docs: maybe_docs(vec![" Some doc", " Some doc"]),
				},
				PalletConstantMetadata {
					name: "some_extra_extra",
					ty: meta_type::<u64>(),
					value: vec![0, 0, 0, 0, 0, 0, 0, 0],
					docs: maybe_docs(vec![" Some doc"]),
				},
				PalletConstantMetadata {
					name: "SomeExtraRename",
					ty: meta_type::<u64>(),
					value: vec![0, 0, 0, 0, 0, 0, 0, 0],
					docs: maybe_docs(vec![" Some doc"]),
				},
			],
			error: Some(PalletErrorMetadata { ty: meta_type::<pallet::Error<Runtime>>() }),
		},
		PalletMetadata {
			index: 2,
			name: "Example2",
			storage: Some(PalletStorageMetadata {
				prefix: "Example2",
				entries: vec![
					StorageEntryMetadata {
						name: "SomeValue",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Plain(meta_type::<Vec<u32>>()),
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "SomeCountedStorageMap",
						modifier: StorageEntryModifier::Optional,
						ty: StorageEntryType::Map {
							hashers: vec![StorageHasher::Twox64Concat],
							key: meta_type::<u8>(),
							value: meta_type::<u32>(),
						},
						default: vec![0],
						docs: vec![],
					},
					StorageEntryMetadata {
						name: "CounterForSomeCountedStorageMap",
						modifier: StorageEntryModifier::Default,
						ty: StorageEntryType::Plain(meta_type::<u32>()),
						default: vec![0, 0, 0, 0],
						docs: maybe_docs(vec!["Counter for the related counted storage map"]),
					},
				],
			}),
			calls: None,
			event: Some(PalletEventMetadata { ty: meta_type::<pallet2::Event>() }),
			constants: vec![],
			error: None,
		},
		#[cfg(feature = "frame-feature-testing")]
		PalletMetadata {
			index: 3,
			name: "Example3",
			storage: None,
			calls: None,
			event: None,
			constants: vec![],
			error: None,
		},
		#[cfg(feature = "frame-feature-testing-2")]
		PalletMetadata {
			index: 5,
			name: "Example5",
			storage: None,
			calls: None,
			event: None,
			constants: vec![],
			error: None,
		},
	];

	let empty_doc = pallets[0].event.as_ref().unwrap().ty.type_info().docs().is_empty() &&
		pallets[0].error.as_ref().unwrap().ty.type_info().docs().is_empty() &&
		pallets[0].calls.as_ref().unwrap().ty.type_info().docs().is_empty();

	if cfg!(feature = "no-metadata-docs") {
		assert!(empty_doc)
	} else {
		assert!(!empty_doc)
	}

	let extrinsic = ExtrinsicMetadata {
		ty: meta_type::<UncheckedExtrinsic>(),
		version: 4,
		signed_extensions: vec![SignedExtensionMetadata {
			identifier: "UnitSignedExtension",
			ty: meta_type::<()>(),
			additional_signed: meta_type::<()>(),
		}],
	};

	let expected_metadata: RuntimeMetadataPrefixed =
		RuntimeMetadataLastVersion::new(pallets, extrinsic, meta_type::<Runtime>()).into();
	let expected_metadata = match expected_metadata.1 {
		RuntimeMetadata::V14(metadata) => metadata,
		_ => panic!("metadata has been bumped, test needs to be updated"),
	};

	let actual_metadata = match Runtime::metadata().1 {
		RuntimeMetadata::V14(metadata) => metadata,
		_ => panic!("metadata has been bumped, test needs to be updated"),
	};

	pretty_assertions::assert_eq!(actual_metadata.pallets, expected_metadata.pallets);
}

#[test]
fn metadata_at_version() {
	use frame_support::metadata::*;
	use sp_core::Decode;

	let metadata = Runtime::metadata();
	let at_metadata = match Runtime::metadata_at_version(LATEST_METADATA_VERSION) {
		Some(opaque) => {
			let bytes = &*opaque;
			let metadata: RuntimeMetadataPrefixed = Decode::decode(&mut &bytes[..]).unwrap();
			metadata
		},
		_ => panic!("metadata has been bumped, test needs to be updated"),
	};

	assert_eq!(metadata, at_metadata);
}

#[test]
fn metadata_versions() {
	assert_eq!(vec![LATEST_METADATA_VERSION], Runtime::metadata_versions());
}

#[test]
fn metadata_ir_pallet_runtime_docs() {
	let ir = Runtime::metadata_ir();
	let pallet = ir
		.pallets
		.iter()
		.find(|pallet| pallet.name == "Example")
		.expect("Pallet should be present");

	let readme = "Support code for the runtime.\n\nLicense: Apache-2.0";
	let expected = vec![" Pallet documentation", readme, readme];
	assert_eq!(pallet.docs, expected);
}

#[test]
fn test_pallet_runtime_docs() {
	let docs = crate::pallet::Pallet::<Runtime>::pallet_documentation_metadata();
	let readme = "Support code for the runtime.\n\nLicense: Apache-2.0";
	let expected = vec![" Pallet documentation", readme, readme];
	assert_eq!(docs, expected);
}

#[test]
fn test_pallet_info_access() {
	assert_eq!(<System as frame_support::traits::PalletInfoAccess>::name(), "System");
	assert_eq!(<Example as frame_support::traits::PalletInfoAccess>::name(), "Example");
	assert_eq!(<Example2 as frame_support::traits::PalletInfoAccess>::name(), "Example2");

	assert_eq!(<System as frame_support::traits::PalletInfoAccess>::index(), 0);
	assert_eq!(<Example as frame_support::traits::PalletInfoAccess>::index(), 1);
	assert_eq!(<Example2 as frame_support::traits::PalletInfoAccess>::index(), 2);
}

#[test]
fn test_storage_info() {
	use frame_support::{
		storage::storage_prefix as prefix,
		traits::{StorageInfo, StorageInfoTrait},
	};

	// Storage max size is calculated by adding up all the hasher size, the key type size and the
	// value type size
	assert_eq!(
		Example::storage_info(),
		vec![
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"ValueWhereClause".to_vec(),
				prefix: prefix(b"Example", b"ValueWhereClause").to_vec(),
				max_values: Some(1),
				max_size: Some(8),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"Value".to_vec(),
				prefix: prefix(b"Example", b"Value").to_vec(),
				max_values: Some(1),
				max_size: Some(4),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"Value2".to_vec(),
				prefix: prefix(b"Example", b"Value2").to_vec(),
				max_values: Some(1),
				max_size: Some(8),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"Map".to_vec(),
				prefix: prefix(b"Example", b"Map").to_vec(),
				max_values: None,
				max_size: Some(16 + 1 + 2),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"Map2".to_vec(),
				prefix: prefix(b"Example", b"Map2").to_vec(),
				max_values: Some(3),
				max_size: Some(8 + 2 + 4),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"Map3".to_vec(),
				prefix: prefix(b"Example", b"Map3").to_vec(),
				max_values: None,
				max_size: Some(16 + 4 + 8),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"DoubleMap".to_vec(),
				prefix: prefix(b"Example", b"DoubleMap").to_vec(),
				max_values: None,
				max_size: Some(16 + 1 + 8 + 2 + 4),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"DoubleMap2".to_vec(),
				prefix: prefix(b"Example", b"DoubleMap2").to_vec(),
				max_values: Some(5),
				max_size: Some(8 + 2 + 16 + 4 + 8),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"DoubleMap3".to_vec(),
				prefix: prefix(b"Example", b"DoubleMap3").to_vec(),
				max_values: None,
				max_size: Some(16 + 4 + 8 + 8 + 16),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"NMap".to_vec(),
				prefix: prefix(b"Example", b"NMap").to_vec(),
				max_values: None,
				max_size: Some(16 + 1 + 4),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"NMap2".to_vec(),
				prefix: prefix(b"Example", b"NMap2").to_vec(),
				max_values: Some(11),
				max_size: Some(8 + 2 + 16 + 4 + 8),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"NMap3".to_vec(),
				prefix: prefix(b"Example", b"NMap3").to_vec(),
				max_values: None,
				max_size: Some(16 + 1 + 8 + 2 + 16),
			},
			#[cfg(feature = "frame-feature-testing")]
			{
				StorageInfo {
					pallet_name: b"Example".to_vec(),
					storage_name: b"ConditionalValue".to_vec(),
					prefix: prefix(b"Example", b"ConditionalValue").to_vec(),
					max_values: Some(1),
					max_size: Some(4),
				}
			},
			#[cfg(feature = "frame-feature-testing")]
			{
				StorageInfo {
					pallet_name: b"Example".to_vec(),
					storage_name: b"ConditionalMap".to_vec(),
					prefix: prefix(b"Example", b"ConditionalMap").to_vec(),
					max_values: Some(12),
					max_size: Some(8 + 2 + 4),
				}
			},
			#[cfg(feature = "frame-feature-testing")]
			{
				StorageInfo {
					pallet_name: b"Example".to_vec(),
					storage_name: b"ConditionalDoubleMap".to_vec(),
					prefix: prefix(b"Example", b"ConditionalDoubleMap").to_vec(),
					max_values: None,
					max_size: Some(16 + 1 + 8 + 2 + 4),
				}
			},
			#[cfg(feature = "frame-feature-testing")]
			{
				StorageInfo {
					pallet_name: b"Example".to_vec(),
					storage_name: b"ConditionalNMap".to_vec(),
					prefix: prefix(b"Example", b"ConditionalNMap").to_vec(),
					max_values: None,
					max_size: Some(16 + 1 + 8 + 2 + 4),
				}
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"RenamedCountedMap".to_vec(),
				prefix: prefix(b"Example", b"RenamedCountedMap").to_vec(),
				max_values: None,
				max_size: Some(8 + 1 + 4),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"CounterForRenamedCountedMap".to_vec(),
				prefix: prefix(b"Example", b"CounterForRenamedCountedMap").to_vec(),
				max_values: Some(1),
				max_size: Some(4),
			},
			StorageInfo {
				pallet_name: b"Example".to_vec(),
				storage_name: b"Unbounded".to_vec(),
				prefix: prefix(b"Example", b"Unbounded").to_vec(),
				max_values: Some(1),
				max_size: None,
			},
		],
	);

	assert_eq!(
		Example2::storage_info(),
		vec![
			StorageInfo {
				pallet_name: b"Example2".to_vec(),
				storage_name: b"SomeValue".to_vec(),
				prefix: prefix(b"Example2", b"SomeValue").to_vec(),
				max_values: Some(1),
				max_size: None,
			},
			StorageInfo {
				pallet_name: b"Example2".to_vec(),
				storage_name: b"SomeCountedStorageMap".to_vec(),
				prefix: prefix(b"Example2", b"SomeCountedStorageMap").to_vec(),
				max_values: None,
				max_size: None,
			},
			StorageInfo {
				pallet_name: b"Example2".to_vec(),
				storage_name: b"CounterForSomeCountedStorageMap".to_vec(),
				prefix: prefix(b"Example2", b"CounterForSomeCountedStorageMap").to_vec(),
				max_values: Some(1),
				max_size: Some(4),
			},
		],
	);
}

#[test]
fn assert_type_all_pallets_reversed_with_system_first_is_correct() {
	// Just ensure the 2 types are same.
	#[allow(deprecated)]
	fn _a(_t: AllPalletsReversedWithSystemFirst) {}
	#[cfg(all(not(feature = "frame-feature-testing"), not(feature = "frame-feature-testing-2")))]
	fn _b(t: (System, Example4, Example2, Example)) {
		_a(t)
	}
	#[cfg(all(feature = "frame-feature-testing", not(feature = "frame-feature-testing-2")))]
	fn _b(t: (System, Example4, Example3, Example2, Example)) {
		_a(t)
	}

	#[cfg(all(not(feature = "frame-feature-testing"), feature = "frame-feature-testing-2"))]
	fn _b(t: (System, Example5, Example4, Example2, Example)) {
		_a(t)
	}

	#[cfg(all(feature = "frame-feature-testing", feature = "frame-feature-testing-2"))]
	fn _b(t: (System, Example5, Example4, Example3, Example2, Example)) {
		_a(t)
	}
}

#[test]
fn assert_type_all_pallets_with_system_is_correct() {
	// Just ensure the 2 types are same.
	fn _a(_t: AllPalletsWithSystem) {}
	#[cfg(all(not(feature = "frame-feature-testing"), not(feature = "frame-feature-testing-2")))]
	fn _b(t: (System, Example, Example2, Example4)) {
		_a(t)
	}
	#[cfg(all(feature = "frame-feature-testing", not(feature = "frame-feature-testing-2")))]
	fn _b(t: (System, Example, Example2, Example3, Example4)) {
		_a(t)
	}
	#[cfg(all(not(feature = "frame-feature-testing"), feature = "frame-feature-testing-2"))]
	fn _b(t: (System, Example, Example2, Example4, Example5)) {
		_a(t)
	}
	#[cfg(all(feature = "frame-feature-testing", feature = "frame-feature-testing-2"))]
	fn _b(t: (System, Example, Example2, Example3, Example4, Example5)) {
		_a(t)
	}
}

#[test]
fn assert_type_all_pallets_without_system_is_correct() {
	// Just ensure the 2 types are same.
	fn _a(_t: AllPalletsWithoutSystem) {}
	#[cfg(all(not(feature = "frame-feature-testing"), not(feature = "frame-feature-testing-2")))]
	fn _b(t: (Example, Example2, Example4)) {
		_a(t)
	}
	#[cfg(all(feature = "frame-feature-testing", not(feature = "frame-feature-testing-2")))]
	fn _b(t: (Example, Example2, Example3, Example4)) {
		_a(t)
	}
	#[cfg(all(not(feature = "frame-feature-testing"), feature = "frame-feature-testing-2"))]
	fn _b(t: (Example, Example2, Example4, Example5)) {
		_a(t)
	}
	#[cfg(all(feature = "frame-feature-testing", feature = "frame-feature-testing-2"))]
	fn _b(t: (Example, Example2, Example3, Example4, Example5)) {
		_a(t)
	}
}

#[test]
fn assert_type_all_pallets_with_system_reversed_is_correct() {
	// Just ensure the 2 types are same.
	#[allow(deprecated)]
	fn _a(_t: AllPalletsWithSystemReversed) {}
	#[cfg(all(not(feature = "frame-feature-testing"), not(feature = "frame-feature-testing-2")))]
	fn _b(t: (Example4, Example2, Example, System)) {
		_a(t)
	}
	#[cfg(all(feature = "frame-feature-testing", not(feature = "frame-feature-testing-2")))]
	fn _b(t: (Example4, Example3, Example2, Example, System)) {
		_a(t)
	}
	#[cfg(all(not(feature = "frame-feature-testing"), feature = "frame-feature-testing-2"))]
	fn _b(t: (Example5, Example4, Example2, Example, System)) {
		_a(t)
	}
	#[cfg(all(feature = "frame-feature-testing", feature = "frame-feature-testing-2"))]
	fn _b(t: (Example5, Example4, Example3, Example2, Example, System)) {
		_a(t)
	}
}

#[test]
fn assert_type_all_pallets_without_system_reversed_is_correct() {
	// Just ensure the 2 types are same.
	#[allow(deprecated)]
	fn _a(_t: AllPalletsWithoutSystemReversed) {}
	#[cfg(all(not(feature = "frame-feature-testing"), not(feature = "frame-feature-testing-2")))]
	fn _b(t: (Example4, Example2, Example)) {
		_a(t)
	}
	#[cfg(all(feature = "frame-feature-testing", not(feature = "frame-feature-testing-2")))]
	fn _b(t: (Example4, Example3, Example2, Example)) {
		_a(t)
	}
	#[cfg(all(not(feature = "frame-feature-testing"), feature = "frame-feature-testing-2"))]
	fn _b(t: (Example5, Example4, Example2, Example)) {
		_a(t)
	}
	#[cfg(all(feature = "frame-feature-testing", feature = "frame-feature-testing-2"))]
	fn _b(t: (Example5, Example4, Example3, Example2, Example)) {
		_a(t)
	}
}

#[test]
fn test_storage_alias() {
	use frame_support::Twox64Concat;

	#[frame_support::storage_alias]
	type Value<T: pallet::Config>
	where
		<T as frame_system::Config>::AccountId: From<SomeType1> + SomeAssociation1,
	= StorageValue<pallet::Pallet<T>, u32, ValueQuery>;

	#[frame_support::storage_alias]
	type SomeCountedStorageMap<T: pallet2::Config>
	where
		<T as frame_system::Config>::AccountId: From<SomeType1> + SomeAssociation1,
	= CountedStorageMap<pallet2::Pallet<T>, Twox64Concat, u8, u32>;

	TestExternalities::default().execute_with(|| {
		pallet::Value::<Runtime>::put(10);
		assert_eq!(10, Value::<Runtime>::get());

		pallet2::SomeCountedStorageMap::<Runtime>::insert(10, 100);
		assert_eq!(Some(100), SomeCountedStorageMap::<Runtime>::get(10));
		assert_eq!(1, SomeCountedStorageMap::<Runtime>::count());
		assert_eq!(
			SomeCountedStorageMap::<Runtime>::storage_info(),
			pallet2::SomeCountedStorageMap::<Runtime>::storage_info()
		);
	})
}

#[test]
fn test_dispatch_context() {
	TestExternalities::default().execute_with(|| {
		// By default there is no context
		assert!(with_context::<(), _>(|_| ()).is_none());

		// When not using `dispatch`, there should be no dispatch context
		assert_eq!(
			DispatchError::Unavailable,
			Example::check_for_dispatch_context(RuntimeOrigin::root()).unwrap_err(),
		);

		// When using `dispatch`, there should be a dispatch context
		assert_ok!(RuntimeCall::from(pallet::Call::<Runtime>::check_for_dispatch_context {})
			.dispatch(RuntimeOrigin::root()));
	});
}
