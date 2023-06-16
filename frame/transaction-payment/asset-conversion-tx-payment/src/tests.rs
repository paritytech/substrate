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

use frame_support::{
	assert_ok,
	dispatch::{DispatchInfo, PostDispatchInfo},
	pallet_prelude::*,
	traits::{fungible::Inspect, fungibles::Mutate},
	weights::Weight,
};
use frame_system as system;
use mock::{ExtrinsicBaseWeight, *};
use pallet_asset_conversion::NativeOrAssetId;
use pallet_balances::Call as BalancesCall;
use sp_runtime::traits::StaticLookup;

const CALL: &<Runtime as frame_system::Config>::RuntimeCall =
	&RuntimeCall::Balances(BalancesCall::transfer_allow_death { dest: 2, value: 69 });

pub struct ExtBuilder {
	balance_factor: u64,
	base_weight: Weight,
	byte_fee: u64,
	weight_to_fee: u64,
}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self {
			balance_factor: 1,
			base_weight: Weight::from_parts(0, 0),
			byte_fee: 1,
			weight_to_fee: 1,
		}
	}
}

impl ExtBuilder {
	pub fn base_weight(mut self, base_weight: Weight) -> Self {
		self.base_weight = base_weight;
		self
	}
	pub fn balance_factor(mut self, factor: u64) -> Self {
		self.balance_factor = factor;
		self
	}
	fn set_constants(&self) {
		ExtrinsicBaseWeight::mutate(|v| *v = self.base_weight);
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

fn setup_lp(asset_id: u32, balance_factor: u64) {
	let lp_provider = 5;
	assert_ok!(Balances::force_set_balance(
		RuntimeOrigin::root(),
		lp_provider,
		10_000 * balance_factor
	));
	let lp_provider_account = <Runtime as system::Config>::Lookup::unlookup(lp_provider);
	assert_ok!(Assets::mint_into(asset_id.into(), &lp_provider_account, 10_000 * balance_factor));

	let token_1 = NativeOrAssetId::Native;
	let token_2 = NativeOrAssetId::Asset(asset_id);
	assert_ok!(AssetConversion::create_pool(RuntimeOrigin::signed(lp_provider), token_1, token_2));

	assert_ok!(AssetConversion::add_liquidity(
		RuntimeOrigin::signed(lp_provider),
		token_1,
		token_2,
		1_000 * balance_factor,  // 1 desired
		10_000 * balance_factor, // 2 desired
		1,                       // 1 min
		1,                       // 2 min
		lp_provider_account,
	));
}

const WEIGHT_5: Weight = Weight::from_parts(5, 0);
const WEIGHT_50: Weight = Weight::from_parts(50, 0);
const WEIGHT_100: Weight = Weight::from_parts(100, 0);

#[test]
fn transaction_payment_in_native_possible() {
	let base_weight = 5;
	let balance_factor = 100;
	ExtBuilder::default()
		.balance_factor(balance_factor)
		.base_weight(Weight::from_parts(base_weight, 0))
		.build()
		.execute_with(|| {
			let len = 10;
			let pre = ChargeAssetTxPayment::<Runtime>::from(0, None)
				.pre_dispatch(&1, CALL, &info_from_weight(WEIGHT_5), len)
				.unwrap();
			let initial_balance = 10 * balance_factor;
			assert_eq!(Balances::free_balance(1), initial_balance - 5 - 5 - 10);

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(WEIGHT_5),
				&default_post_info(),
				len,
				&Ok(())
			));
			assert_eq!(Balances::free_balance(1), initial_balance - 5 - 5 - 10);

			let pre = ChargeAssetTxPayment::<Runtime>::from(5 /* tipped */, None)
				.pre_dispatch(&2, CALL, &info_from_weight(WEIGHT_100), len)
				.unwrap();
			let initial_balance_for_2 = 20 * balance_factor;

			assert_eq!(Balances::free_balance(2), initial_balance_for_2 - 5 - 10 - 100 - 5);
			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(WEIGHT_100),
				&post_info_from_weight(WEIGHT_50),
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
		.base_weight(Weight::from_parts(base_weight, 0))
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 2;
			assert_ok!(Assets::force_create(
				RuntimeOrigin::root(),
				asset_id.into(),
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			// mint into the caller account
			let caller = 1;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 1000;

			assert_ok!(Assets::mint_into(asset_id.into(), &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);

			let len = 10;
			let tx_weight = 5;

			setup_lp(asset_id, balance_factor);

			let fee_in_native = base_weight + tx_weight + len as u64;
			let input_quote = AssetConversion::quote_price_tokens_for_exact_tokens(
				NativeOrAssetId::Asset(asset_id),
				NativeOrAssetId::Native,
				fee_in_native,
				true,
			);
			assert_eq!(input_quote, Some(201));

			let fee_in_asset = input_quote.unwrap();
			assert_eq!(Assets::balance(asset_id, caller), balance);

			let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(WEIGHT_5), len)
				.unwrap();
			// assert that native balance is not used
			assert_eq!(Balances::free_balance(caller), 10 * balance_factor);

			// check that fee was charged in the given asset
			assert_eq!(Assets::balance(asset_id, caller), balance - fee_in_asset);

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(WEIGHT_5), // estimated tx weight
				&default_post_info(),        // weight actually used == estimated
				len,
				&Ok(())
			));

			assert_eq!(Assets::balance(asset_id, caller), balance - fee_in_asset);
			assert_eq!(TipUnbalancedAmount::get(), 0);
			assert_eq!(FeeUnbalancedAmount::get(), fee_in_native);
		});
}

#[test]
fn transaction_payment_in_asset_fails_if_no_pool_for_that_asset() {
	let base_weight = 5;
	let balance_factor = 100;
	ExtBuilder::default()
		.balance_factor(balance_factor)
		.base_weight(Weight::from_parts(base_weight, 0))
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 2;
			assert_ok!(Assets::force_create(
				RuntimeOrigin::root(),
				asset_id.into(),
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			// mint into the caller account
			let caller = 1;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 1000;

			assert_ok!(Assets::mint_into(asset_id.into(), &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);

			let len = 10;
			let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id)).pre_dispatch(
				&caller,
				CALL,
				&info_from_weight(WEIGHT_5),
				len,
			);

			// As there is no pool in the dex set up for this asset, conversion should fail.
			assert!(pre.is_err());
		});
}

#[test]
fn transaction_payment_without_fee() {
	let base_weight = 5;
	let balance_factor = 100;
	ExtBuilder::default()
		.balance_factor(balance_factor)
		.base_weight(Weight::from_parts(base_weight, 0))
		.build()
		.execute_with(|| {
			let caller = 1;

			// create the asset
			let asset_id = 1;
			let balance = 1000;
			let min_balance = 2;

			assert_ok!(Assets::force_create(
				RuntimeOrigin::root(),
				asset_id.into(),
				42,   /* owner */
				true, /* is_sufficient */
				min_balance,
			));

			setup_lp(asset_id, balance_factor);

			// mint into the caller account
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			assert_ok!(Assets::mint_into(asset_id.into(), &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);

			let weight = 5;
			let len = 10;
			let fee_in_native = base_weight + weight + len as u64;
			let input_quote = AssetConversion::quote_price_tokens_for_exact_tokens(
				NativeOrAssetId::Asset(asset_id),
				NativeOrAssetId::Native,
				fee_in_native,
				true,
			);
			assert_eq!(input_quote, Some(201));

			let fee_in_asset = input_quote.unwrap();
			let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(WEIGHT_5), len)
				.unwrap();

			// assert that native balance is not used
			assert_eq!(Balances::free_balance(caller), 10 * balance_factor);
			// check that fee was charged in the given asset
			assert_eq!(Assets::balance(asset_id, caller), balance - fee_in_asset);

			let refund = AssetConversion::quote_price_exact_tokens_for_tokens(
				NativeOrAssetId::Native,
				NativeOrAssetId::Asset(asset_id),
				fee_in_native,
				true,
			)
			.unwrap();
			assert_eq!(refund, 199);

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(WEIGHT_5),
				&post_info_from_pays(Pays::No),
				len,
				&Ok(())
			));

			// caller should get refunded
			assert_eq!(Assets::balance(asset_id, caller), balance - fee_in_asset + refund);
			assert_eq!(Balances::free_balance(caller), 10 * balance_factor);
		});
}

#[test]
fn asset_transaction_payment_with_tip_and_refund() {
	let base_weight = 5;
	let balance_factor = 100;
	ExtBuilder::default()
		.balance_factor(balance_factor)
		.base_weight(Weight::from_parts(base_weight, 0))
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 2;
			assert_ok!(Assets::force_create(
				RuntimeOrigin::root(),
				asset_id.into(),
				42,   /* owner */
				true, /* is_sufficient */
				min_balance,
			));

			setup_lp(asset_id, balance_factor);

			// mint into the caller account
			let caller = 2;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 10000;

			assert_ok!(Assets::mint_into(asset_id.into(), &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);

			let weight = 100;
			let tip = 5;
			let len = 10;
			let fee_in_native = base_weight + weight + len as u64 + tip;
			let input_quote = AssetConversion::quote_price_tokens_for_exact_tokens(
				NativeOrAssetId::Asset(asset_id),
				NativeOrAssetId::Native,
				fee_in_native,
				true,
			);
			assert_eq!(input_quote, Some(1206));

			let fee_in_asset = input_quote.unwrap();
			let pre = ChargeAssetTxPayment::<Runtime>::from(tip, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(WEIGHT_100), len)
				.unwrap();
			assert_eq!(Assets::balance(asset_id, caller), balance - fee_in_asset);

			let final_weight = 50;
			let expected_fee = fee_in_native - final_weight - tip;
			let expected_token_refund = AssetConversion::quote_price_exact_tokens_for_tokens(
				NativeOrAssetId::Native,
				NativeOrAssetId::Asset(asset_id),
				fee_in_native - expected_fee - tip,
				true,
			)
			.unwrap();

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(WEIGHT_100),
				&post_info_from_weight(WEIGHT_50),
				len,
				&Ok(())
			));

			assert_eq!(TipUnbalancedAmount::get(), tip);
			assert_eq!(FeeUnbalancedAmount::get(), expected_fee);

			// caller should get refunded
			assert_eq!(
				Assets::balance(asset_id, caller),
				balance - fee_in_asset + expected_token_refund
			);
			assert_eq!(Balances::free_balance(caller), 20 * balance_factor);
		});
}

#[test]
fn payment_from_account_with_only_assets() {
	let base_weight = 5;
	let balance_factor = 100;
	ExtBuilder::default()
		.balance_factor(balance_factor)
		.base_weight(Weight::from_parts(base_weight, 0))
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 2;
			assert_ok!(Assets::force_create(
				RuntimeOrigin::root(),
				asset_id.into(),
				42,   /* owner */
				true, /* is_sufficient */
				min_balance,
			));

			setup_lp(asset_id, balance_factor);

			// mint into the caller account
			let caller = 333;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 1000;

			assert_ok!(Assets::mint_into(asset_id.into(), &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);

			// assert that native balance is not necessary
			assert_eq!(Balances::free_balance(caller), 0);
			let weight = 5;
			let len = 10;

			let fee_in_native = base_weight + weight + len as u64;
			let ed = Balances::minimum_balance();
			let fee_in_asset = AssetConversion::quote_price_tokens_for_exact_tokens(
				NativeOrAssetId::Asset(asset_id),
				NativeOrAssetId::Native,
				fee_in_native + ed,
				true,
			)
			.unwrap();
			assert_eq!(fee_in_asset, 301);

			let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(WEIGHT_5), len)
				.unwrap();
			assert_eq!(Balances::free_balance(caller), ed);
			// check that fee was charged in the given asset
			assert_eq!(Assets::balance(asset_id, caller), balance - fee_in_asset);

			let refund = AssetConversion::quote_price_exact_tokens_for_tokens(
				NativeOrAssetId::Native,
				NativeOrAssetId::Asset(asset_id),
				ed,
				true,
			)
			.unwrap();

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(WEIGHT_5),
				&default_post_info(),
				len,
				&Ok(())
			));
			assert_eq!(Assets::balance(asset_id, caller), balance - fee_in_asset + refund);
			assert_eq!(Balances::free_balance(caller), 0);

			assert_eq!(TipUnbalancedAmount::get(), 0);
			assert_eq!(FeeUnbalancedAmount::get(), fee_in_native);
		});
}

#[test]
fn converted_fee_is_never_zero_if_input_fee_is_not() {
	let base_weight = 1;
	let balance_factor = 100;
	ExtBuilder::default()
		.balance_factor(balance_factor)
		.base_weight(Weight::from_parts(base_weight, 0))
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 1;
			assert_ok!(Assets::force_create(
				RuntimeOrigin::root(),
				asset_id.into(),
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			setup_lp(asset_id, balance_factor);

			// mint into the caller account
			let caller = 2;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 1000;

			assert_ok!(Assets::mint_into(asset_id.into(), &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);

			let weight = 1;
			let len = 1;

			// there will be no conversion when the fee is zero
			{
				let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
					.pre_dispatch(&caller, CALL, &info_from_pays(Pays::No), len)
					.unwrap();
				// `Pays::No` implies there are no fees
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

			// validate even a small fee gets converted to asset.
			let fee_in_native = base_weight + weight + len as u64;
			let fee_in_asset = AssetConversion::quote_price_tokens_for_exact_tokens(
				NativeOrAssetId::Asset(asset_id),
				NativeOrAssetId::Native,
				fee_in_native,
				true,
			)
			.unwrap();

			let pre = ChargeAssetTxPayment::<Runtime>::from(0, Some(asset_id))
				.pre_dispatch(&caller, CALL, &info_from_weight(Weight::from_parts(weight, 0)), len)
				.unwrap();
			assert_eq!(Assets::balance(asset_id, caller), balance - fee_in_asset);

			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				Some(pre),
				&info_from_weight(Weight::from_parts(weight, 0)),
				&default_post_info(),
				len,
				&Ok(())
			));
			assert_eq!(Assets::balance(asset_id, caller), balance - fee_in_asset);
		});
}

#[test]
fn post_dispatch_fee_is_zero_if_pre_dispatch_fee_is_zero() {
	let base_weight = 1;
	ExtBuilder::default()
		.balance_factor(100)
		.base_weight(Weight::from_parts(base_weight, 0))
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 100;
			assert_ok!(Assets::force_create(
				RuntimeOrigin::root(),
				asset_id.into(),
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			// mint into the caller account
			let caller = 333;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 1000;

			assert_ok!(Assets::mint_into(asset_id.into(), &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);

			let weight = 1;
			let len = 1;
			let fee = base_weight + weight + len as u64;

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
		.base_weight(Weight::from_parts(base_weight, 0))
		.build()
		.execute_with(|| {
			// create the asset
			let asset_id = 1;
			let min_balance = 100;
			assert_ok!(Assets::force_create(
				RuntimeOrigin::root(),
				asset_id.into(),
				42,   /* owner */
				true, /* is_sufficient */
				min_balance
			));

			// mint into the caller account
			let caller = 333;
			let beneficiary = <Runtime as system::Config>::Lookup::unlookup(caller);
			let balance = 1000;

			assert_ok!(Assets::mint_into(asset_id.into(), &beneficiary, balance));
			assert_eq!(Assets::balance(asset_id, caller), balance);

			let weight = 1;
			let len = 1;
			ChargeAssetTxPayment::<Runtime>::pre_dispatch_unsigned(
				CALL,
				&info_from_weight(Weight::from_parts(weight, 0)),
				len,
			)
			.unwrap();

			assert_eq!(Assets::balance(asset_id, caller), balance);

			// `Pays::Yes` on post-dispatch does not mean we pay (we never charge more than the
			// initial fee)
			assert_ok!(ChargeAssetTxPayment::<Runtime>::post_dispatch(
				None,
				&info_from_weight(Weight::from_parts(weight, 0)),
				&post_info_from_pays(Pays::Yes),
				len,
				&Ok(())
			));
			assert_eq!(Assets::balance(asset_id, caller), balance);
		});
}
