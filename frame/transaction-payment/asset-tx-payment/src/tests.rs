// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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
use crate as pallet_asset_tx_payment;

use frame_support::{
	assert_ok,
	pallet_prelude::*,
	parameter_types,
	traits::{fungibles::Mutate, ConstU32, ConstU64, ConstU8, FindAuthor},
	weights::{DispatchClass, DispatchInfo, PostDispatchInfo, Weight, WeightToFee as WeightToFeeT},
	ConsensusEngineId,
};
use frame_system as system;
use frame_system::EnsureRoot;
use pallet_balances::Call as BalancesCall;
use pallet_transaction_payment::CurrencyAdapter;
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, ConvertInto, IdentityLookup, SaturatedConversion, StaticLookup},
};
use std::cell::RefCell;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Runtime>;
type Block = frame_system::mocking::MockBlock<Runtime>;
type Balance = u64;
type AccountId = u64;

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		TransactionPayment: pallet_transaction_payment::{Pallet, Storage, Event<T>},
		Assets: pallet_assets::{Pallet, Call, Storage, Event<T>},
		Authorship: pallet_authorship::{Pallet, Call, Storage},
		AssetTxPayment: pallet_asset_tx_payment::{Pallet, Event<T>},
	}
);

const CALL: &<Runtime as frame_system::Config>::Call =
	&Call::Balances(BalancesCall::transfer { dest: 2, value: 69 });

thread_local! {
	static EXTRINSIC_BASE_WEIGHT: RefCell<u64> = RefCell::new(0);
}

pub struct BlockWeights;
impl Get<frame_system::limits::BlockWeights> for BlockWeights {
	fn get() -> frame_system::limits::BlockWeights {
		frame_system::limits::BlockWeights::builder()
			.base_block(0)
			.for_class(DispatchClass::all(), |weights| {
				weights.base_extrinsic = EXTRINSIC_BASE_WEIGHT.with(|v| *v.borrow()).into();
			})
			.for_class(DispatchClass::non_mandatory(), |weights| {
				weights.max_total = 1024.into();
			})
			.build_or_panic()
	}
}

parameter_types! {
	pub static WeightToFee: u64 = 1;
	pub static TransactionByteFee: u64 = 1;
}

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = BlockWeights;
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

parameter_types! {
	pub const ExistentialDeposit: u64 = 10;
}

impl pallet_balances::Config for Runtime {
	type Balance = Balance;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ConstU64<10>;
	type AccountStore = System;
	type MaxLocks = ();
	type WeightInfo = ();
	type MaxReserves = ConstU32<50>;
	type ReserveIdentifier = [u8; 8];
}

impl WeightToFeeT for WeightToFee {
	type Balance = u64;

	fn weight_to_fee(weight: &Weight) -> Self::Balance {
		Self::Balance::saturated_from(*weight).saturating_mul(WEIGHT_TO_FEE.with(|v| *v.borrow()))
	}
}

impl WeightToFeeT for TransactionByteFee {
	type Balance = u64;

	fn weight_to_fee(weight: &Weight) -> Self::Balance {
		Self::Balance::saturated_from(*weight)
			.saturating_mul(TRANSACTION_BYTE_FEE.with(|v| *v.borrow()))
	}
}

impl pallet_transaction_payment::Config for Runtime {
	type Event = Event;
	type OnChargeTransaction = CurrencyAdapter<Balances, ()>;
	type WeightToFee = WeightToFee;
	type LengthToFee = TransactionByteFee;
	type FeeMultiplierUpdate = ();
	type OperationalFeeMultiplier = ConstU8<5>;
}

impl pallet_assets::Config for Runtime {
	type Event = Event;
	type Balance = Balance;
	type AssetId = u32;
	type Currency = Balances;
	type ForceOrigin = EnsureRoot<AccountId>;
	type AssetDeposit = ConstU64<2>;
	type AssetAccountDeposit = ConstU64<2>;
	type MetadataDepositBase = ConstU64<0>;
	type MetadataDepositPerByte = ConstU64<0>;
	type ApprovalDeposit = ConstU64<0>;
	type StringLimit = ConstU32<20>;
	type Freezer = ();
	type Extra = ();
	type WeightInfo = ();
}

pub struct HardcodedAuthor;
const BLOCK_AUTHOR: AccountId = 1234;
impl FindAuthor<AccountId> for HardcodedAuthor {
	fn find_author<'a, I>(_: I) -> Option<AccountId>
	where
		I: 'a + IntoIterator<Item = (ConsensusEngineId, &'a [u8])>,
	{
		Some(BLOCK_AUTHOR)
	}
}

impl pallet_authorship::Config for Runtime {
	type FindAuthor = HardcodedAuthor;
	type UncleGenerations = ();
	type FilterUncle = ();
	type EventHandler = ();
}

pub struct CreditToBlockAuthor;
impl HandleCredit<AccountId, Assets> for CreditToBlockAuthor {
	fn handle_credit(credit: CreditOf<AccountId, Assets>) {
		if let Some(author) = pallet_authorship::Pallet::<Runtime>::author() {
			// What to do in case paying the author fails (e.g. because `fee < min_balance`)
			// default: drop the result which will trigger the `OnDrop` of the imbalance.
			let _ = <Assets as Balanced<AccountId>>::resolve(&author, credit);
		}
	}
}

impl Config for Runtime {
	type Event = Event;
	type Fungibles = Assets;
	type OnChargeAssetTransaction = FungiblesAdapter<
		pallet_assets::BalanceToAssetBalance<Balances, Runtime, ConvertInto>,
		CreditToBlockAuthor,
	>;
}

pub struct ExtBuilder {
	balance_factor: u64,
	base_weight: u64,
	byte_fee: u64,
	weight_to_fee: u64,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self { balance_factor: 1, base_weight: 0, byte_fee: 1, weight_to_fee: 1 }
	}
}

impl ExtBuilder {
	pub fn base_weight(mut self, base_weight: u64) -> Self {
		self.base_weight = base_weight;
		self
	}
	pub fn balance_factor(mut self, factor: u64) -> Self {
		self.balance_factor = factor;
		self
	}
	fn set_constants(&self) {
		EXTRINSIC_BASE_WEIGHT.with(|v| *v.borrow_mut() = self.base_weight);
		TRANSACTION_BYTE_FEE.with(|v| *v.borrow_mut() = self.byte_fee);
		WEIGHT_TO_FEE.with(|v| *v.borrow_mut() = self.weight_to_fee);
	}
	pub fn build(self) -> sp_io::TestExternalities {
		self.set_constants();
		let mut t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
		pallet_balances::GenesisConfig::<Runtime> {
			balances: if self.balance_factor > 0 {
				vec![
					(1, 10 * self.balance_factor),
					(2, 20 * self.balance_factor),
					(3, 30 * self.balance_factor),
					(4, 40 * self.balance_factor),
					(5, 50 * self.balance_factor),
					(6, 60 * self.balance_factor),
				]
			} else {
				vec![]
			},
		}
		.assimilate_storage(&mut t)
		.unwrap();
		t.into()
	}
}

/// create a transaction info struct from weight. Handy to avoid building the whole struct.
pub fn info_from_weight(w: Weight) -> DispatchInfo {
	// pays_fee: Pays::Yes -- class: DispatchClass::Normal
	DispatchInfo { weight: w, ..Default::default() }
}

fn post_info_from_weight(w: Weight) -> PostDispatchInfo {
	PostDispatchInfo { actual_weight: Some(w), pays_fee: Default::default() }
}

fn info_from_pays(p: Pays) -> DispatchInfo {
	DispatchInfo { pays_fee: p, ..Default::default() }
}

fn post_info_from_pays(p: Pays) -> PostDispatchInfo {
	PostDispatchInfo { actual_weight: None, pays_fee: p }
}

fn default_post_info() -> PostDispatchInfo {
	PostDispatchInfo { actual_weight: None, pays_fee: Default::default() }
}

#[test]
fn transaction_payment_in_native_possible() {
	let balance_factor = 100;
	ExtBuilder::default()
		.balance_factor(balance_factor)
		.base_weight(5)
		.build()
		.execute_with(|| {
			let len = 10;
			let pre = ChargeAssetTxPayment::<Runtime>::from(0, None)
				.pre_dispatch(&1, CALL, &info_from_weight(5), len)
				.unwrap();
			let initial_balance = 10 * balance_factor;
			assert_eq!(Balances::free_balance(1), initial_balance - 5 - 5 - 10);

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(5),
				&default_post_info(),
				len,
				&Ok(())
			));
			assert_eq!(Balances::free_balance(1), initial_balance - 5 - 5 - 10);

			let pre = ChargeAssetTxPayment::<Runtime>::from(5 /* tipped */, None)
				.pre_dispatch(&2, CALL, &info_from_weight(100), len)
				.unwrap();
			let initial_balance_for_2 = 20 * balance_factor;
			assert_eq!(Balances::free_balance(2), initial_balance_for_2 - 5 - 10 - 100 - 5);

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(100),
				&post_info_from_weight(50),
				len,
				&Ok(())
			));
			assert_eq!(Balances::free_balance(2), initial_balance_for_2 - 5 - 10 - 50 - 5);
		});
}

#[test]
fn transaction_payment_in_asset_possible() {
	let base_weight = 5;
	let balance_factor = 100;
	ExtBuilder::default()
		.balance_factor(balance_factor)
		.base_weight(base_weight)
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 2;
			assert_ok!(Assets::force_create(
				Origin::root(),
				asset_id,
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			// mint into the caller account
			let caller = 1;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 100;
			assert_ok!(Assets::mint_into(asset_id, &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);
			let weight = 5;
			let len = 10;
			// we convert the from weight to fee based on the ratio between asset min balance and
			// existential deposit
			let fee = (base_weight + weight + len as u64) * min_balance / ExistentialDeposit::get();
			let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(weight), len)
				.unwrap();
			// assert that native balance is not used
			assert_eq!(Balances::free_balance(caller), 10 * balance_factor);
			// check that fee was charged in the given asset
			assert_eq!(Assets::balance(asset_id, caller), balance - fee);
			assert_eq!(Assets::balance(asset_id, BLOCK_AUTHOR), 0);

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(weight),
				&default_post_info(),
				len,
				&Ok(())
			));
			assert_eq!(Assets::balance(asset_id, caller), balance - fee);
			// check that the block author gets rewarded
			assert_eq!(Assets::balance(asset_id, BLOCK_AUTHOR), fee);
		});
}

#[test]
fn transaction_payment_without_fee() {
	let base_weight = 5;
	let balance_factor = 100;
	ExtBuilder::default()
		.balance_factor(balance_factor)
		.base_weight(base_weight)
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 2;
			assert_ok!(Assets::force_create(
				Origin::root(),
				asset_id,
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			// mint into the caller account
			let caller = 1;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 100;
			assert_ok!(Assets::mint_into(asset_id, &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);
			let weight = 5;
			let len = 10;
			// we convert the from weight to fee based on the ratio between asset min balance and
			// existential deposit
			let fee = (base_weight + weight + len as u64) * min_balance / ExistentialDeposit::get();
			let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(weight), len)
				.unwrap();
			// assert that native balance is not used
			assert_eq!(Balances::free_balance(caller), 10 * balance_factor);
			// check that fee was charged in the given asset
			assert_eq!(Assets::balance(asset_id, caller), balance - fee);
			assert_eq!(Assets::balance(asset_id, BLOCK_AUTHOR), 0);

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(weight),
				&post_info_from_pays(Pays::No),
				len,
				&Ok(())
			));
			// caller should be refunded
			assert_eq!(Assets::balance(asset_id, caller), balance);
			// check that the block author did not get rewarded
			assert_eq!(Assets::balance(asset_id, BLOCK_AUTHOR), 0);
		});
}

#[test]
fn asset_transaction_payment_with_tip_and_refund() {
	let base_weight = 5;
	ExtBuilder::default()
		.balance_factor(100)
		.base_weight(base_weight)
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 2;
			assert_ok!(Assets::force_create(
				Origin::root(),
				asset_id,
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			// mint into the caller account
			let caller = 2;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 1000;
			assert_ok!(Assets::mint_into(asset_id, &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);
			let weight = 100;
			let tip = 5;
			let len = 10;
			// we convert the from weight to fee based on the ratio between asset min balance and
			// existential deposit
			let fee_with_tip =
				(base_weight + weight + len as u64 + tip) * min_balance / ExistentialDeposit::get();
			let pre = ChargeAssetTxPayment::<Runtime>::from(tip, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(weight), len)
				.unwrap();
			assert_eq!(Assets::balance(asset_id, caller), balance - fee_with_tip);

			let final_weight = 50;
			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(weight),
				&post_info_from_weight(final_weight),
				len,
				&Ok(())
			));
			let final_fee =
				fee_with_tip - (weight - final_weight) * min_balance / ExistentialDeposit::get();
			assert_eq!(Assets::balance(asset_id, caller), balance - (final_fee));
			assert_eq!(Assets::balance(asset_id, BLOCK_AUTHOR), final_fee);
		});
}

#[test]
fn payment_from_account_with_only_assets() {
	let base_weight = 5;
	ExtBuilder::default()
		.balance_factor(100)
		.base_weight(base_weight)
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 2;
			assert_ok!(Assets::force_create(
				Origin::root(),
				asset_id,
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			// mint into the caller account
			let caller = 333;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 100;
			assert_ok!(Assets::mint_into(asset_id, &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);
			// assert that native balance is not necessary
			assert_eq!(Balances::free_balance(caller), 0);
			let weight = 5;
			let len = 10;
			// we convert the from weight to fee based on the ratio between asset min balance and
			// existential deposit
			let fee = (base_weight + weight + len as u64) * min_balance / ExistentialDeposit::get();
			let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(weight), len)
				.unwrap();
			assert_eq!(Balances::free_balance(caller), 0);
			// check that fee was charged in the given asset
			assert_eq!(Assets::balance(asset_id, caller), balance - fee);

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(weight),
				&default_post_info(),
				len,
				&Ok(())
			));
			assert_eq!(Assets::balance(asset_id, caller), balance - fee);
			assert_eq!(Balances::free_balance(caller), 0);
		});
}

#[test]
fn payment_only_with_existing_sufficient_asset() {
	let base_weight = 5;
	ExtBuilder::default()
		.balance_factor(100)
		.base_weight(base_weight)
		.build()
		.execute_with(|| {
			let asset_id = 1;
			let caller = 1;
			let weight = 5;
			let len = 10;
			// pre_dispatch fails for non-existent asset
			assert!(ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(weight), len)
				.is_err());

			// create the non-sufficient asset
			let min_balance = 2;
			assert_ok!(Assets::force_create(
				Origin::root(),
				asset_id,
				42,    /* owner */
				false, /* is_sufficient */
				min_balance
			));
			// pre_dispatch fails for non-sufficient asset
			assert!(ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(weight), len)
				.is_err());
		});
}

#[test]
fn converted_fee_is_never_zero_if_input_fee_is_not() {
	let base_weight = 1;
	ExtBuilder::default()
		.balance_factor(100)
		.base_weight(base_weight)
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 1;
			assert_ok!(Assets::force_create(
				Origin::root(),
				asset_id,
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			// mint into the caller account
			let caller = 333;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 100;
			assert_ok!(Assets::mint_into(asset_id, &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);
			let weight = 1;
			let len = 1;
			// we convert the from weight to fee based on the ratio between asset min balance and
			// existential deposit
			let fee = (base_weight + weight + len as u64) * min_balance / ExistentialDeposit::get();
			// naive fee calculation would round down to zero
			assert_eq!(fee, 0);
			{
				let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
					.pre_dispatch(&caller, CALL, &info_from_pays(Pays::No), len)
					.unwrap();
				// `Pays::No` still implies no fees
				assert_eq!(Assets::balance(asset_id, caller), balance);

				assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
					Some(pre),
					&info_from_pays(Pays::No),
					&post_info_from_pays(Pays::No),
					len,
					&Ok(())
				));
				assert_eq!(Assets::balance(asset_id, caller), balance);
			}
			let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(weight), len)
				.unwrap();
			// check that at least one coin was charged in the given asset
			assert_eq!(Assets::balance(asset_id, caller), balance - 1);

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(weight),
				&default_post_info(),
				len,
				&Ok(())
			));
			assert_eq!(Assets::balance(asset_id, caller), balance - 1);
		});
}

#[test]
fn post_dispatch_fee_is_zero_if_pre_dispatch_fee_is_zero() {
	let base_weight = 1;
	ExtBuilder::default()
		.balance_factor(100)
		.base_weight(base_weight)
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 100;
			assert_ok!(Assets::force_create(
				Origin::root(),
				asset_id,
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			// mint into the caller account
			let caller = 333;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 100;
			assert_ok!(Assets::mint_into(asset_id, &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);
			let weight = 1;
			let len = 1;
			// we convert the from weight to fee based on the ratio between asset min balance and
			// existential deposit
			let fee = (base_weight + weight + len as u64) * min_balance / ExistentialDeposit::get();
			// calculated fee is greater than 0
			assert!(fee > 0);
			let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_pays(Pays::No), len)
				.unwrap();
			// `Pays::No` implies no pre-dispatch fees
			assert_eq!(Assets::balance(asset_id, caller), balance);
			let (_tip, _who, initial_payment, _asset_id) = &pre;
			let not_paying = match initial_payment {
				&InitialPayment::Nothing => true,
				_ => false,
			};
			assert!(not_paying, "initial payment should be Nothing if we pass Pays::No");

			// `Pays::Yes` on post-dispatch does not mean we pay (we never charge more than the
			// initial fee)
			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_pays(Pays::No),
				&post_info_from_pays(Pays::Yes),
				len,
				&Ok(())
			));
			assert_eq!(Assets::balance(asset_id, caller), balance);
		});
}

#[test]
fn post_dispatch_fee_is_zero_if_unsigned_pre_dispatch_fee_is_zero() {
	let base_weight = 1;
	ExtBuilder::default()
		.balance_factor(100)
		.base_weight(base_weight)
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 100;
			assert_ok!(Assets::force_create(
				Origin::root(),
				asset_id,
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			// mint into the caller account
			let caller = 333;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 100;
			assert_ok!(Assets::mint_into(asset_id, &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);
			let weight = 1;
			let len = 1;
			ChargeAssetTxPayment::<Runtime>::pre_dispatch_unsigned(
				CALL,
				&info_from_weight(weight),
				len,
			)
			.unwrap();

			assert_eq!(Assets::balance(asset_id, caller), balance);

			// `Pays::Yes` on post-dispatch does not mean we pay (we never charge more than the
			// initial fee)
			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				None,
				&info_from_weight(weight),
				&post_info_from_pays(Pays::Yes),
				len,
				&Ok(())
			));
			assert_eq!(Assets::balance(asset_id, caller), balance);
		});
}
