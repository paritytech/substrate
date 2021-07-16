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

pub trait SomeAssociation {
	type A: frame_support::dispatch::Parameter + Default;
}
impl SomeAssociation for u64 {
	type A = u64;
}

mod pallet_old {
	use frame_support::{
		decl_storage, decl_error, decl_event, decl_module, weights::Weight, traits::Get, Parameter
	};
	use frame_system::ensure_root;
	use super::SomeAssociation;

	pub trait Config: frame_system::Config {
		type SomeConst: Get<Self::Balance>;
		type Balance: Parameter + codec::HasCompact + From<u32> + Into<Weight> + Default
			+ SomeAssociation;
		type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>;
	}

	decl_storage! {
		trait Store for Module<T: Config> as Example {
			/// Some documentation
			Dummy get(fn dummy) config(): Option<T::Balance>;
			Bar get(fn bar) config(): map hasher(blake2_128_concat) T::AccountId => T::Balance;
			Foo get(fn foo) config(): T::Balance = 3.into();
			Double get(fn double): double_map
				hasher(blake2_128_concat) u32,
				hasher(twox_64_concat) u64
				=> <T::Balance as SomeAssociation>::A;
		}
	}

	decl_event!(
		pub enum Event<T> where Balance = <T as Config>::Balance {
			/// Dummy event, just here so there's a generic type that's used.
			Dummy(Balance),
		}
	);

	decl_module! {
		pub struct Module<T: Config> for enum Call where origin: T::Origin {
			type Error = Error<T>;
			fn deposit_event() = default;
			const SomeConst: T::Balance = T::SomeConst::get();

			#[weight = <T::Balance as Into<Weight>>::into(new_value.clone())]
			fn set_dummy(origin, #[compact] new_value: T::Balance) {
				ensure_root(origin)?;

				<Dummy<T>>::put(&new_value);
				Self::deposit_event(RawEvent::Dummy(new_value));
			}

			fn on_initialize(_n: T::BlockNumber) -> Weight {
				<Dummy<T>>::put(T::Balance::from(10));
				10
			}

			fn on_finalize(_n: T::BlockNumber) {
				<Dummy<T>>::put(T::Balance::from(11));
			}
		}
	}

	decl_error! {
		pub enum Error for Module<T: Config> {
			/// Some wrong behavior
			Wrong,
		}
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::SomeAssociation;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use frame_system::ensure_root;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Balance: Parameter + codec::HasCompact + From<u32> + Into<Weight> + Default
			+ MaybeSerializeDeserialize + SomeAssociation;
		#[pallet::constant]
		type SomeConst: Get<Self::Balance>;
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {
		fn on_initialize(_n: T::BlockNumber) -> Weight {
			<Dummy<T>>::put(T::Balance::from(10));
			10
		}

		fn on_finalize(_n: T::BlockNumber) {
			<Dummy<T>>::put(T::Balance::from(11));
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(<T::Balance as Into<Weight>>::into(new_value.clone()))]
		pub fn set_dummy(
			origin: OriginFor<T>,
			#[pallet::compact] new_value: T::Balance
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;

			<Dummy<T>>::put(&new_value);
			Self::deposit_event(Event::Dummy(new_value));

			Ok(().into())
		}
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Some wrong behavior
		Wrong,
	}

	#[pallet::event]
	#[pallet::generate_deposit(fn deposit_event)]
	#[pallet::metadata(T::Balance = "Balance")]
	pub enum Event<T: Config> {
		/// Dummy event, just here so there's a generic type that's used.
		Dummy(T::Balance),
	}

	#[pallet::storage]
	/// Some documentation
	type Dummy<T: Config> = StorageValue<_, T::Balance, OptionQuery>;

	#[pallet::storage]
	type Bar<T: Config> = StorageMap<_, Blake2_128Concat, T::AccountId, T::Balance, ValueQuery>;

	#[pallet::type_value] pub fn OnFooEmpty<T: Config>() -> T::Balance { 3.into() }
	#[pallet::storage]
	type Foo<T: Config> = StorageValue<_, T::Balance, ValueQuery, OnFooEmpty<T>>;

	#[pallet::storage]
	type Double<T: Config> = StorageDoubleMap<
		_, Blake2_128Concat, u32, Twox64Concat, u64, <T::Balance as SomeAssociation>::A, ValueQuery
	>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		dummy: Option<T::Balance>,
		bar: Vec<(T::AccountId, T::Balance)>,
		foo: T::Balance,
	}

	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			GenesisConfig {
				dummy: Default::default(),
				bar: Default::default(),
				foo: OnFooEmpty::<T>::get(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			if let Some(dummy) = self.dummy.as_ref() {
				<Dummy<T>>::put(dummy);
			}
			for (k, v) in &self.bar {
				<Bar<T>>::insert(k, v);
			}
			<Foo<T>>::put(&self.foo);
		}
	}
}

frame_support::parameter_types!(
	pub const SomeConst: u64 = 10;
	pub const BlockHashCount: u32 = 250;
);

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::AllowAll;
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
	type BlockHashCount = BlockHashCount;
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
}
impl pallet::Config for Runtime {
	type Event = Event;
	type SomeConst = SomeConst;
	type Balance = u64;
}
impl pallet_old::Config for Runtime {
	type Event = Event;
	type SomeConst = SomeConst;
	type Balance = u64;
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
		System: frame_system::{Pallet, Call, Event<T>},
		// NOTE: name Example here is needed in order to have same module prefix
		Example: pallet::{Pallet, Call, Event<T>, Config<T>, Storage},
		PalletOld: pallet_old::{Pallet, Call, Event<T>, Config<T>, Storage},
	}
);

#[cfg(test)]
mod test {
	use super::Runtime;
	use super::pallet;
	use super::pallet_old;
	use codec::{Decode, Encode};

	#[test]
	fn metadata() {
		let metadata = Runtime::metadata();
		let modules = match metadata.1 {
			frame_metadata::RuntimeMetadata::V13(frame_metadata::RuntimeMetadataV13 {
				modules: frame_metadata::DecodeDifferent::Encode(m),
				..
			}) => m,
			_ => unreachable!(),
		};
		pretty_assertions::assert_eq!(modules[1].storage, modules[2].storage);
		pretty_assertions::assert_eq!(modules[1].calls, modules[2].calls);
		pretty_assertions::assert_eq!(modules[1].event, modules[2].event);
		pretty_assertions::assert_eq!(modules[1].constants, modules[2].constants);
		pretty_assertions::assert_eq!(modules[1].errors, modules[2].errors);
	}

	#[test]
	fn types() {
		assert_eq!(
			pallet_old::Event::<Runtime>::decode(
				&mut &pallet::Event::<Runtime>::Dummy(10).encode()[..]
			).unwrap(),
			pallet_old::Event::<Runtime>::Dummy(10),
		);

		assert_eq!(
			pallet_old::Call::<Runtime>::decode(
				&mut &pallet::Call::<Runtime>::set_dummy(10).encode()[..]
			).unwrap(),
			pallet_old::Call::<Runtime>::set_dummy(10),
		);
	}
}
