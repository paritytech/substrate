// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use frame_support::{parameter_types, traits::Contains, PalletId};
use orml_traits::parameter_type_with_key;
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{AccountIdConversion, BlakeTwo256, ConvertInto, IdentityLookup},
};
use sp_std::convert::TryFrom;

use super::*;
use crate as pallet_vesting_mangata;

pub const NATIVE_CURRENCY_ID: u32 = 0;

pub(crate) type Balance = u128;
pub(crate) type AccountId = u64;
pub(crate) type TokenId = u32;
pub(crate) type Amount = i128;
pub(crate) type BlockNumber = u64;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Tokens: orml_tokens::{Pallet, Storage, Call, Event<T>, Config<T>},
		Vesting: pallet_vesting_mangata::{Pallet, Call, Storage, Event<T>, Config<T>},
	}
);

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(Weight::from_ref_time(1024));
}
impl frame_system::Config for Test {
	type AccountData = ();
	type AccountId = AccountId;
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockHashCount = BlockHashCount;
	type BlockLength = ();
	type BlockNumber = BlockNumber;
	type BlockWeights = ();
	type Call = Call;
	type DbWeight = ();
	type Event = Event;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type Header = Header;
	type Index = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type OnKilledAccount = ();
	type OnNewAccount = ();
	type OnSetCode = ();
	type Origin = Origin;
	type PalletInfo = PalletInfo;
	type SS58Prefix = ();
	type SystemWeightInfo = ();
	type Version = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}
parameter_type_with_key! {
	pub ExistentialDeposits: |currency_id: TokenId| -> Balance {
		match currency_id {
			_ => 0,
		}
	};
}

pub struct DustRemovalWhitelist;
impl Contains<AccountId> for DustRemovalWhitelist {
	fn contains(a: &AccountId) -> bool {
		*a == TreasuryAccount::get()
	}
}

parameter_types! {
	pub const NativeCurrencyId: u32 = NATIVE_CURRENCY_ID;
	pub const TreasuryPalletId: PalletId = PalletId(*b"py/trsry");
	pub TreasuryAccount: AccountId = TreasuryPalletId::get().into_account_truncating();
	pub const MaxLocks: u32 = 50;
}

impl orml_tokens::Config for Test {
	type Event = Event;
	type Balance = Balance;
	type Amount = Amount;
	type CurrencyId = TokenId;
	type WeightInfo = ();
	type ExistentialDeposits = ExistentialDeposits;
	type OnDust = ();
	type MaxLocks = MaxLocks;
	type DustRemovalWhitelist = DustRemovalWhitelist;
}
parameter_types! {
	pub const MinVestedTransfer: u64 = 256 * 2;
	pub static ExistentialDeposit: u64 = 0;
}
impl Config for Test {
	type BlockNumberToBalance = ConvertInto;
	type Tokens = orml_tokens::MultiTokenCurrencyAdapter<Test>;
	type Event = Event;
	const MAX_VESTING_SCHEDULES: u32 = 3;
	type MinVestedTransfer = MinVestedTransfer;
	type WeightInfo = ();
}

pub struct ExtBuilder {
	existential_deposit: Balance,
	vesting_genesis_config: Option<Vec<(AccountId, TokenId, u64, u64, Balance)>>,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self { existential_deposit: 1, vesting_genesis_config: None }
	}
}

impl ExtBuilder {
	pub fn existential_deposit(mut self, existential_deposit: Balance) -> Self {
		self.existential_deposit = existential_deposit;
		self
	}

	pub fn vesting_genesis_config(
		mut self,
		config: Vec<(AccountId, TokenId, u64, u64, Balance)>,
	) -> Self {
		self.vesting_genesis_config = Some(config);
		self
	}

	pub fn build(self) -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

		orml_tokens::GenesisConfig::<Test> {
			tokens_endowment: vec![
				(1, NATIVE_CURRENCY_ID, 10 * self.existential_deposit),
				(2, NATIVE_CURRENCY_ID, 20 * self.existential_deposit),
				(3, NATIVE_CURRENCY_ID, 30 * self.existential_deposit),
				(4, NATIVE_CURRENCY_ID, 40 * self.existential_deposit),
				(12, NATIVE_CURRENCY_ID, 10 * self.existential_deposit),
				(13, NATIVE_CURRENCY_ID, 9999 * self.existential_deposit),
			],
			created_tokens_for_staking: Default::default(),
		}
		.assimilate_storage(&mut t)
		.expect("Tokens storage can be assimilated");

		let vesting = if let Some(vesting_config) = self.vesting_genesis_config {
			vesting_config
		} else {
			vec![
				(
					1,
					NATIVE_CURRENCY_ID,
					0,
					10,
					(10 * self.existential_deposit) - (5 * self.existential_deposit),
				),
				(2, NATIVE_CURRENCY_ID, 10, 20, 20 * self.existential_deposit),
				(
					12,
					NATIVE_CURRENCY_ID,
					10,
					20,
					(10 * self.existential_deposit) - (5 * self.existential_deposit),
				),
			]
		};

		pallet_vesting_mangata::GenesisConfig::<Test> { vesting }
			.assimilate_storage(&mut t)
			.unwrap();
		let mut ext = sp_io::TestExternalities::new(t);
		ext.execute_with(|| System::set_block_number(1));
		ext
	}
}

pub(crate) fn usable_native_balance<T: frame_system::Config + orml_tokens::Config>(
	who: <T as frame_system::Config>::AccountId,
) -> <T as orml_tokens::Config>::Balance {
	let orml_account = <orml_tokens::Pallet<T>>::accounts::<
		<T as frame_system::Config>::AccountId,
		<T as orml_tokens::Config>::CurrencyId,
	>(who.into(), NATIVE_CURRENCY_ID.into());
	orml_account.free.saturating_sub(orml_account.frozen)
}
