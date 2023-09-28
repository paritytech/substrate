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
use crate as pallet_interface;
use crate::mock::interfaces::pip20::{BalanceSelectable, CurrencySelectable};
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::dispatch::TypeInfo;
use frame_support::interface::{CallResult, Select, Selector, SelectorResult, ViewResult};
use frame_support::{
	assert_noop, assert_ok, ord_parameter_types, parameter_types,
	traits::{ConstU32, ConstU64, EitherOfDiverse},
	BoundedVec,
};
use frame_system::{EnsureRoot, EnsureSignedBy};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BadOrigin, BlakeTwo256, IdentityLookup},
	RuntimeDebug,
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<MockRuntime>;
type Block = frame_system::mocking::MockBlock<MockRuntime>;

type Balance = u64;
type AccountId = u64;

#[derive(
	Encode,
	Decode,
	codec::MaxEncodedLen,
	sp_core::RuntimeDebug,
	scale_info::TypeInfo,
	Clone,
	PartialEq,
	Eq,
)]
pub enum CurrencyId {
	Native,
	Other,
}

mod interfaces {
	#[frame_support::interface]
	pub mod pip20 {
		use frame_support::{
			dispatch::DispatchResult,
			interface::{CallResult, Select, Selector, SelectorResult, ViewResult},
			Parameter,
		};
		use sp_core::H256;
		use sp_runtime::traits::Member;

		pub type CurrencySelectable = H256;
		pub type AccountIdSelectable = [u8; 32];
		pub type BalanceSelectable = u128;

		#[interface::definition]
		pub trait Pip20: frame_system::Config {
			/// A means for converting between from a [u8; 32] to the native chains account id.
			type SelectAccount: Selector<
				Selectable = AccountIdSelectable,
				Selected = Self::AccountId,
			>;

			/// The chains native currency type.
			type Currency: Parameter + Member;

			/// A means for converting between from a `H256` to the chains native currency.
			type SelectCurrency: Selector<
				Selectable = CurrencySelectable,
				Selected = Self::Currency,
			>;

			/// The chains native balance type.
			type Balance: Parameter + Member;

			/// A means for converting between from a u128 to the chains native balance.
			type SelectBalance: Selector<Selectable = BalanceSelectable, Selected = Self::Balance>;

			#[interface::view]
			#[interface::view_index(0)]
			fn free_balance(
				currency: Select<Self::SelectCurrency>,
				who: Select<Self::SelectAccount>,
			) -> ViewResult<BalanceSelectable>;

			#[interface::view]
			#[interface::view_index(1)]
			fn balances(
				who: Select<Self::SelectAccount>,
			) -> ViewResult<Vec<(CurrencySelectable, BalanceSelectable)>>;

			#[interface::call]
			#[interface::call_index(0)]
			#[interface::weight(0)]
			fn transfer(
				origin: Self::RuntimeOrigin,
				currency: Select<Self::SelectCurrency>,
				recv: Select<Self::SelectAccount>,
				amount: Select<Self::SelectBalance>,
			) -> CallResult;

			#[interface::call]
			#[interface::call_index(3)]
			#[interface::weight(0)]
			fn burn(
				origin: Self::RuntimeOrigin,
				currency: Select<Self::SelectCurrency>,
				from: Select<Self::SelectAccount>,
				amount: Select<Self::SelectBalance>,
			) -> CallResult;

			#[interface::call]
			#[interface::call_index(1)]
			#[interface::weight(0)]
			fn approve(
				origin: Self::RuntimeOrigin,
				currency: Select<Self::SelectCurrency>,
				recv: Select<Self::SelectAccount>,
				amount: Select<Self::SelectBalance>,
			) -> CallResult;
		}
	}

	#[frame_support::interface]
	pub mod pip42 {
		use frame_support::interface;
		use frame_support::interface::CallResult;
		use sp_core::Get;
		use sp_runtime::BoundedVec;

		#[interface::definition]
		pub trait Pip42: frame_system::Config {
			type MaxRemark: Get<u32>;

			#[interface::call]
			#[interface::call_index(0)]
			#[interface::weight(0)]
			fn remark(
				origin: Self::RuntimeOrigin,
				bytes: BoundedVec<u8, Self::MaxRemark>,
			) -> CallResult;
		}
	}
}

frame_support::construct_runtime!(
	pub enum MockRuntime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		// NOTE: The interface pallet should live at the same index
		//       for all chains, if this should make the lives of wallets, etc.
		//       easier.
		Interface: pallet_interface::{Pallet, Call, Event<T>} = 255
	}
);

impl frame_system::Config for MockRuntime {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type RuntimeCall = RuntimeCall;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

impl pallet_balances::Config for MockRuntime {
	type Balance = Balance;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
}

impl pallet_interface::Config for MockRuntime {
	type RuntimeEvent = RuntimeEvent;
	type Interface = InterfaceCall;
}

pub struct AccountSelector;
impl Selector for AccountSelector {
	type Selectable = interfaces::pip20::AccountIdSelectable;
	type Selected = AccountId;

	fn select(selectable: Self::Selectable) -> SelectorResult<Self::Selected> {
		todo!()
	}
}

pub struct CurrencySelector;
impl Selector for CurrencySelector {
	type Selectable = interfaces::pip20::CurrencySelectable;
	type Selected = CurrencyId;

	fn select(selectable: Self::Selectable) -> SelectorResult<Self::Selected> {
		todo!()
	}
}

pub struct BalanceSelector;
impl Selector for BalanceSelector {
	type Selectable = interfaces::pip20::BalanceSelectable;
	type Selected = Balance;

	fn select(selectable: Self::Selectable) -> SelectorResult<Self::Selected> {
		todo!()
	}
}

impl interfaces::pip20::Pip20 for MockRuntime {
	/// A means for converting between from a [u8; 32] to the native chains account id.
	type SelectAccount = AccountSelector;

	/// The chains native currency type.
	type Currency = CurrencyId;

	/// A means for converting between from a `H256` to the chains native currency.
	type SelectCurrency = CurrencySelector;

	/// The chains native balance type.
	type Balance = Balance;

	/// A means for converting between from a u128 to the chains native balance.
	type SelectBalance = BalanceSelector;

	fn free_balance(
		currency: Select<Self::SelectCurrency>,
		who: Select<Self::SelectAccount>,
	) -> ViewResult<BalanceSelectable> {
		todo!()
	}

	fn balances(
		who: Select<Self::SelectAccount>,
	) -> ViewResult<Vec<(CurrencySelectable, BalanceSelectable)>> {
		todo!()
	}

	fn transfer(
		origin: Self::RuntimeOrigin,
		currency: Select<Self::SelectCurrency>,
		recv: Select<Self::SelectAccount>,
		amount: Select<Self::SelectBalance>,
	) -> CallResult {
		todo!()
	}

	fn burn(
		origin: Self::RuntimeOrigin,
		currency: Select<Self::SelectCurrency>,
		from: Select<Self::SelectAccount>,
		amount: Select<Self::SelectBalance>,
	) -> CallResult {
		todo!()
	}

	fn approve(
		origin: Self::RuntimeOrigin,
		currency: Select<Self::SelectCurrency>,
		recv: Select<Self::SelectAccount>,
		amount: Select<Self::SelectBalance>,
	) -> CallResult {
		todo!()
	}
}

impl interfaces::pip42::Pip42 for MockRuntime {
	type MaxRemark = ConstU32<64>;

	fn remark(origin: Self::RuntimeOrigin, bytes: BoundedVec<u8, Self::MaxRemark>) -> CallResult {
		todo!()
	}
}

#[frame_support::call_entry(MockRuntime)]
//#[derive(Encode, Decode, RuntimeDebug, MaxEncodedLen, TypeInfo, PartialEq, Eq)]
pub enum InterfaceCall {
	#[call_entry::index(20)]
	Pip20(interfaces::pip20::Call<MockRuntime>),
	#[call_entry::index(42)]
	Pip42(interfaces::pip42::Call<MockRuntime>),
}

#[frame_support::view_entry]
pub enum InterfaceView {
	#[view_entry::index(20)]
	Pip20(interfaces::pip20::View<MockRuntime>),
}

/// Executive: handles dispatch to the various modules.
pub type Executive = frame_executive::Executive<
	MockRuntime,
	Block,
	frame_system::ChainContext<MockRuntime>,
	MockRuntime,
	AllPalletsWithSystem,
	// We don't run migrations on the development runtime
	(),
>;

sp_api::impl_runtime_apis! {
	impl sp_api::Core<Block> for MockRuntime {
		fn version() -> sp_api::RuntimeVersion {
			todo!()
		}

		fn execute_block(block: Block) {
			todo!()
		}

		fn initialize_block(header: &<Block as sp_runtime::traits::Block>::Header) {
			todo!()
		}
	}

	impl sp_api::Metadata<Block> for MockRuntime {
		fn metadata() -> sp_core::OpaqueMetadata {
			sp_core::OpaqueMetadata::new(MockRuntime::metadata().into())
		}
	}

	// NOTE:  This is the location where we use the `enum InterfaceView` that
	//        is annotated with the `#[frame_support::view_entry]`
	//        macro.
	impl frame_support::interface::Interface<Block, InterfaceView> for MockRuntime {
		fn view(view: InterfaceView) -> ViewResult<Vec<u8>> {
			frame_support::interface::View::view(view)
		}
	}
}
