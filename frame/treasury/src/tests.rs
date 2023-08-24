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

//! Treasury pallet tests.

#![cfg(test)]

use core::{cell::RefCell, marker::PhantomData};
use sp_core::H256;
use sp_runtime::{
	traits::{BadOrigin, BlakeTwo256, Dispatchable, IdentityLookup},
	BuildStorage,
};

use frame_support::{
	assert_err_ignore_postinfo, assert_noop, assert_ok,
	pallet_prelude::Pays,
	parameter_types,
	traits::{
		tokens::{ConversionFromAssetBalance, PaymentStatus},
		ConstU32, ConstU64, OnInitialize,
	},
	PalletId,
};

use super::*;
use crate as treasury;

type Block = frame_system::mocking::MockBlock<Test>;
type UtilityCall = pallet_utility::Call<Test>;
type TreasuryCall = crate::Call<Test>;

frame_support::construct_runtime!(
	pub enum Test
	{
		System: frame_system::{Pallet, Call, Config<T>, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Treasury: treasury::{Pallet, Call, Storage, Config<T>, Event<T>},
		Utility: pallet_utility,
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Nonce = u64;
	type RuntimeCall = RuntimeCall;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u128; // u64 is not enough to hold bytes used to generate bounty account
	type Lookup = IdentityLookup<Self::AccountId>;
	type Block = Block;
	type RuntimeEvent = RuntimeEvent;
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
impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u64;
	type RuntimeEvent = RuntimeEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type RuntimeHoldReason = ();
	type MaxHolds = ();
}

impl pallet_utility::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type RuntimeCall = RuntimeCall;
	type PalletsOrigin = OriginCaller;
	type WeightInfo = ();
}

thread_local! {
	pub static PAID: RefCell<BTreeMap<(u128, u32), u64>> = RefCell::new(BTreeMap::new());
	pub static STATUS: RefCell<BTreeMap<u64, PaymentStatus>> = RefCell::new(BTreeMap::new());
	pub static LAST_ID: RefCell<u64> = RefCell::new(0u64);
}

/// paid balance for a given account and asset ids
fn paid(who: u128, asset_id: u32) -> u64 {
	PAID.with(|p| p.borrow().get(&(who, asset_id)).cloned().unwrap_or(0))
}

/// reduce paid balance for a given account and asset ids
fn unpay(who: u128, asset_id: u32, amount: u64) {
	PAID.with(|p| p.borrow_mut().entry((who, asset_id)).or_default().saturating_reduce(amount))
}

/// set status for a given payment id
fn set_status(id: u64, s: PaymentStatus) {
	STATUS.with(|m| m.borrow_mut().insert(id, s));
}

pub struct TestPay;
impl Pay for TestPay {
	type Beneficiary = u128;
	type Balance = u64;
	type Id = u64;
	type AssetKind = u32;
	type Error = ();

	fn pay(
		who: &Self::Beneficiary,
		asset_kind: Self::AssetKind,
		amount: Self::Balance,
	) -> Result<Self::Id, Self::Error> {
		PAID.with(|paid| *paid.borrow_mut().entry((*who, asset_kind)).or_default() += amount);
		Ok(LAST_ID.with(|lid| {
			let x = *lid.borrow();
			lid.replace(x + 1);
			x
		}))
	}
	fn check_payment(id: Self::Id) -> PaymentStatus {
		STATUS.with(|s| s.borrow().get(&id).cloned().unwrap_or(PaymentStatus::Unknown))
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_successful(_: &Self::Beneficiary, _: Self::AssetKind, _: Self::Balance) {}
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_concluded(id: Self::Id) {
		set_status(id, PaymentStatus::Failure)
	}
}

parameter_types! {
	pub const ProposalBond: Permill = Permill::from_percent(5);
	pub const Burn: Permill = Permill::from_percent(50);
	pub const TreasuryPalletId: PalletId = PalletId(*b"py/trsry");
	pub TreasuryAccount: u128 = Treasury::account_id();
	pub const SpendPayoutPeriod: u64 = 5;
}
pub struct TestSpendOrigin;
impl frame_support::traits::EnsureOrigin<RuntimeOrigin> for TestSpendOrigin {
	type Success = u64;
	fn try_origin(o: RuntimeOrigin) -> Result<Self::Success, RuntimeOrigin> {
		Result::<frame_system::RawOrigin<_>, RuntimeOrigin>::from(o).and_then(|o| match o {
			frame_system::RawOrigin::Root => Ok(u64::max_value()),
			frame_system::RawOrigin::Signed(10) => Ok(5),
			frame_system::RawOrigin::Signed(11) => Ok(10),
			frame_system::RawOrigin::Signed(12) => Ok(20),
			frame_system::RawOrigin::Signed(13) => Ok(50),
			r => Err(RuntimeOrigin::from(r)),
		})
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<RuntimeOrigin, ()> {
		Ok(RuntimeOrigin::root())
	}
}

pub struct MulBy<N>(PhantomData<N>);
impl<N: Get<u64>> ConversionFromAssetBalance<u64, u32, u64> for MulBy<N> {
	type Error = ();
	fn from_asset_balance(balance: u64, _asset_id: u32) -> Result<u64, Self::Error> {
		return balance.checked_mul(N::get()).ok_or(())
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_successful(_: u32) {}
}

impl Config for Test {
	type PalletId = TreasuryPalletId;
	type Currency = pallet_balances::Pallet<Test>;
	type ApproveOrigin = frame_system::EnsureRoot<u128>;
	type RejectOrigin = frame_system::EnsureRoot<u128>;
	type RuntimeEvent = RuntimeEvent;
	type OnSlash = ();
	type ProposalBond = ProposalBond;
	type ProposalBondMinimum = ConstU64<1>;
	type ProposalBondMaximum = ();
	type SpendPeriod = ConstU64<2>;
	type Burn = Burn;
	type BurnDestination = (); // Just gets burned.
	type WeightInfo = ();
	type SpendFunds = ();
	type MaxApprovals = ConstU32<100>;
	type SpendOrigin = TestSpendOrigin;
	type AssetKind = u32;
	type Beneficiary = u128;
	type BeneficiaryLookup = IdentityLookup<Self::Beneficiary>;
	type Paymaster = TestPay;
	type BalanceConverter = MulBy<ConstU64<2>>;
	type PayoutPeriod = SpendPayoutPeriod;
	#[cfg(feature = "runtime-benchmarks")]
	type BenchmarkHelper = ();
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
	pallet_balances::GenesisConfig::<Test> {
		// Total issuance will be 200 with treasury account initialized at ED.
		balances: vec![(0, 100), (1, 98), (2, 1)],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	crate::GenesisConfig::<Test>::default().assimilate_storage(&mut t).unwrap();
	t.into()
}

fn get_payment_id(i: SpendIndex) -> Option<u64> {
	let spend = Spends::<Test, _>::get(i).expect("no spend");
	match spend.status {
		PaymentState::Attempted { id } => Some(id),
		_ => None,
	}
}

#[test]
fn genesis_config_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Treasury::pot(), 0);
		assert_eq!(Treasury::proposal_count(), 0);
	});
}

#[test]
fn spend_local_origin_permissioning_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(Treasury::spend_local(RuntimeOrigin::signed(1), 1, 1), BadOrigin);
		assert_noop!(
			Treasury::spend_local(RuntimeOrigin::signed(10), 6, 1),
			Error::<Test>::InsufficientPermission
		);
		assert_noop!(
			Treasury::spend_local(RuntimeOrigin::signed(11), 11, 1),
			Error::<Test>::InsufficientPermission
		);
		assert_noop!(
			Treasury::spend_local(RuntimeOrigin::signed(12), 21, 1),
			Error::<Test>::InsufficientPermission
		);
		assert_noop!(
			Treasury::spend_local(RuntimeOrigin::signed(13), 51, 1),
			Error::<Test>::InsufficientPermission
		);
	});
}

#[docify::export]
#[test]
fn spend_local_origin_works() {
	new_test_ext().execute_with(|| {
		// Check that accumulate works when we have Some value in Dummy already.
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		// approve spend of some amount to beneficiary `6`.
		assert_ok!(Treasury::spend_local(RuntimeOrigin::signed(10), 5, 6));
		assert_ok!(Treasury::spend_local(RuntimeOrigin::signed(10), 5, 6));
		assert_ok!(Treasury::spend_local(RuntimeOrigin::signed(10), 5, 6));
		assert_ok!(Treasury::spend_local(RuntimeOrigin::signed(10), 5, 6));
		assert_ok!(Treasury::spend_local(RuntimeOrigin::signed(11), 10, 6));
		assert_ok!(Treasury::spend_local(RuntimeOrigin::signed(12), 20, 6));
		assert_ok!(Treasury::spend_local(RuntimeOrigin::signed(13), 50, 6));
		// free balance of `6` is zero, spend period has not passed.
		<Treasury as OnInitialize<u64>>::on_initialize(1);
		assert_eq!(Balances::free_balance(6), 0);
		// free balance of `6` is `100`, spend period has passed.
		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Balances::free_balance(6), 100);
		// `100` spent, `1` burned.
		assert_eq!(Treasury::pot(), 0);
	});
}

#[test]
fn minting_works() {
	new_test_ext().execute_with(|| {
		// Check that accumulate works when we have Some value in Dummy already.
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);
	});
}

#[test]
fn spend_proposal_takes_min_deposit() {
	new_test_ext().execute_with(|| {
		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 1, 3)
		});
		assert_eq!(Balances::free_balance(0), 99);
		assert_eq!(Balances::reserved_balance(0), 1);
	});
}

#[test]
fn spend_proposal_takes_proportional_deposit() {
	new_test_ext().execute_with(|| {
		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_eq!(Balances::free_balance(0), 95);
		assert_eq!(Balances::reserved_balance(0), 5);
	});
}

#[test]
fn spend_proposal_fails_when_proposer_poor() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			{
				#[allow(deprecated)]
				Treasury::propose_spend(RuntimeOrigin::signed(2), 100, 3)
			},
			Error::<Test, _>::InsufficientProposersBalance,
		);
	});
}

#[test]
fn accepted_spend_proposal_ignored_outside_spend_period() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 0)
		});

		<Treasury as OnInitialize<u64>>::on_initialize(1);
		assert_eq!(Balances::free_balance(3), 0);
		assert_eq!(Treasury::pot(), 100);
	});
}

#[test]
fn unused_pot_should_diminish() {
	new_test_ext().execute_with(|| {
		let init_total_issuance = Balances::total_issuance();
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Balances::total_issuance(), init_total_issuance + 100);

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Treasury::pot(), 50);
		assert_eq!(Balances::total_issuance(), init_total_issuance + 50);
	});
}

#[test]
fn rejected_spend_proposal_ignored_on_spend_period() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::reject_proposal(RuntimeOrigin::root(), 0)
		});

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Balances::free_balance(3), 0);
		assert_eq!(Treasury::pot(), 50);
	});
}

#[test]
fn reject_already_rejected_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::reject_proposal(RuntimeOrigin::root(), 0)
		});
		assert_noop!(
			{
				#[allow(deprecated)]
				Treasury::reject_proposal(RuntimeOrigin::root(), 0)
			},
			Error::<Test, _>::InvalidIndex
		);
	});
}

#[test]
fn reject_non_existent_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			{
				#[allow(deprecated)]
				Treasury::reject_proposal(RuntimeOrigin::root(), 0)
			},
			Error::<Test, _>::InvalidIndex
		);
	});
}

#[test]
fn accept_non_existent_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			{
				#[allow(deprecated)]
				Treasury::approve_proposal(RuntimeOrigin::root(), 0)
			},
			Error::<Test, _>::InvalidIndex
		);
	});
}

#[test]
fn accept_already_rejected_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::reject_proposal(RuntimeOrigin::root(), 0)
		});
		assert_noop!(
			{
				#[allow(deprecated)]
				Treasury::approve_proposal(RuntimeOrigin::root(), 0)
			},
			Error::<Test, _>::InvalidIndex
		);
	});
}

#[test]
fn accepted_spend_proposal_enacted_on_spend_period() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 0)
		});

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Balances::free_balance(3), 100);
		assert_eq!(Treasury::pot(), 0);
	});
}

#[test]
fn pot_underflow_should_not_diminish() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 150, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 0)
		});

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Treasury::pot(), 100); // Pot hasn't changed

		let _ = Balances::deposit_into_existing(&Treasury::account_id(), 100).unwrap();
		<Treasury as OnInitialize<u64>>::on_initialize(4);
		assert_eq!(Balances::free_balance(3), 150); // Fund has been spent
		assert_eq!(Treasury::pot(), 25); // Pot has finally changed
	});
}

// Treasury account doesn't get deleted if amount approved to spend is all its free balance.
// i.e. pot should not include existential deposit needed for account survival.
#[test]
fn treasury_account_doesnt_get_deleted() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);
		let treasury_balance = Balances::free_balance(&Treasury::account_id());

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), treasury_balance, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 0)
		});

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Treasury::pot(), 100); // Pot hasn't changed

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), Treasury::pot(), 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 1)
		});

		<Treasury as OnInitialize<u64>>::on_initialize(4);
		assert_eq!(Treasury::pot(), 0); // Pot is emptied
		assert_eq!(Balances::free_balance(Treasury::account_id()), 1); // but the account is still there
	});
}

// In case treasury account is not existing then it works fine.
// This is useful for chain that will just update runtime.
#[test]
fn inexistent_account_works() {
	let mut t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
	pallet_balances::GenesisConfig::<Test> { balances: vec![(0, 100), (1, 99), (2, 1)] }
		.assimilate_storage(&mut t)
		.unwrap();
	// Treasury genesis config is not build thus treasury account does not exist
	let mut t: sp_io::TestExternalities = t.into();

	t.execute_with(|| {
		assert_eq!(Balances::free_balance(Treasury::account_id()), 0); // Account does not exist
		assert_eq!(Treasury::pot(), 0); // Pot is empty

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 99, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 0)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 1, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 1)
		});
		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Treasury::pot(), 0); // Pot hasn't changed
		assert_eq!(Balances::free_balance(3), 0); // Balance of `3` hasn't changed

		Balances::make_free_balance_be(&Treasury::account_id(), 100);
		assert_eq!(Treasury::pot(), 99); // Pot now contains funds
		assert_eq!(Balances::free_balance(Treasury::account_id()), 100); // Account does exist

		<Treasury as OnInitialize<u64>>::on_initialize(4);

		assert_eq!(Treasury::pot(), 0); // Pot has changed
		assert_eq!(Balances::free_balance(3), 99); // Balance of `3` has changed
	});
}

#[test]
fn genesis_funding_works() {
	let mut t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
	let initial_funding = 100;
	pallet_balances::GenesisConfig::<Test> {
		// Total issuance will be 200 with treasury account initialized with 100.
		balances: vec![(0, 100), (Treasury::account_id(), initial_funding)],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	crate::GenesisConfig::<Test>::default().assimilate_storage(&mut t).unwrap();
	let mut t: sp_io::TestExternalities = t.into();

	t.execute_with(|| {
		assert_eq!(Balances::free_balance(Treasury::account_id()), initial_funding);
		assert_eq!(Treasury::pot(), initial_funding - Balances::minimum_balance());
	});
}

#[test]
fn max_approvals_limited() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), u64::MAX);
		Balances::make_free_balance_be(&0, u64::MAX);

		for _ in 0..<Test as Config>::MaxApprovals::get() {
			assert_ok!({
				#[allow(deprecated)]
				Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
			});
			assert_ok!({
				#[allow(deprecated)]
				Treasury::approve_proposal(RuntimeOrigin::root(), 0)
			});
		}

		// One too many will fail
		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_noop!(
			{
				#[allow(deprecated)]
				Treasury::approve_proposal(RuntimeOrigin::root(), 0)
			},
			Error::<Test, _>::TooManyApprovals
		);
	});
}

#[test]
fn remove_already_removed_approval_fails() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 0)
		});
		assert_eq!(Treasury::approvals(), vec![0]);
		assert_ok!(Treasury::remove_approval(RuntimeOrigin::root(), 0));
		assert_eq!(Treasury::approvals(), vec![]);

		assert_noop!(
			Treasury::remove_approval(RuntimeOrigin::root(), 0),
			Error::<Test, _>::ProposalNotApproved
		);
	});
}

#[test]
fn spending_local_in_batch_respects_max_total() {
	new_test_ext().execute_with(|| {
		// Respect the `max_total` for the given origin.
		assert_ok!(RuntimeCall::from(UtilityCall::batch_all {
			calls: vec![
				RuntimeCall::from(TreasuryCall::spend_local { amount: 2, beneficiary: 100 }),
				RuntimeCall::from(TreasuryCall::spend_local { amount: 2, beneficiary: 101 })
			]
		})
		.dispatch(RuntimeOrigin::signed(10)));

		assert_err_ignore_postinfo!(
			RuntimeCall::from(UtilityCall::batch_all {
				calls: vec![
					RuntimeCall::from(TreasuryCall::spend_local { amount: 2, beneficiary: 100 }),
					RuntimeCall::from(TreasuryCall::spend_local { amount: 4, beneficiary: 101 })
				]
			})
			.dispatch(RuntimeOrigin::signed(10)),
			Error::<Test, _>::InsufficientPermission
		);
	})
}

#[test]
fn spending_in_batch_respects_max_total() {
	new_test_ext().execute_with(|| {
		// Respect the `max_total` for the given origin.
		assert_ok!(RuntimeCall::from(UtilityCall::batch_all {
			calls: vec![
				RuntimeCall::from(TreasuryCall::spend {
					asset_kind: 1,
					amount: 1,
					beneficiary: 100,
					valid_from: None,
				}),
				RuntimeCall::from(TreasuryCall::spend {
					asset_kind: 1,
					amount: 1,
					beneficiary: 101,
					valid_from: None,
				})
			]
		})
		.dispatch(RuntimeOrigin::signed(10)));

		assert_err_ignore_postinfo!(
			RuntimeCall::from(UtilityCall::batch_all {
				calls: vec![
					RuntimeCall::from(TreasuryCall::spend {
						asset_kind: 1,
						amount: 2,
						beneficiary: 100,
						valid_from: None,
					}),
					RuntimeCall::from(TreasuryCall::spend {
						asset_kind: 1,
						amount: 2,
						beneficiary: 101,
						valid_from: None,
					})
				]
			})
			.dispatch(RuntimeOrigin::signed(10)),
			Error::<Test, _>::InsufficientPermission
		);
	})
}

#[test]
fn spend_origin_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 1, 6, None));
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, None));
		assert_noop!(
			Treasury::spend(RuntimeOrigin::signed(10), 1, 3, 6, None),
			Error::<Test, _>::InsufficientPermission
		);
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(11), 1, 5, 6, None));
		assert_noop!(
			Treasury::spend(RuntimeOrigin::signed(11), 1, 6, 6, None),
			Error::<Test, _>::InsufficientPermission
		);
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(12), 1, 10, 6, None));
		assert_noop!(
			Treasury::spend(RuntimeOrigin::signed(12), 1, 11, 6, None),
			Error::<Test, _>::InsufficientPermission
		);

		assert_eq!(SpendCount::<Test, _>::get(), 4);
		assert_eq!(Spends::<Test, _>::iter().count(), 4);
	});
}

#[test]
fn spend_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, None));

		assert_eq!(SpendCount::<Test, _>::get(), 1);
		assert_eq!(
			Spends::<Test, _>::get(0).unwrap(),
			SpendStatus {
				asset_kind: 1,
				amount: 2,
				beneficiary: 6,
				valid_from: 1,
				expire_at: 6,
				status: PaymentState::Pending,
			}
		);
		System::assert_last_event(
			Event::<Test, _>::AssetSpendApproved {
				index: 0,
				asset_kind: 1,
				amount: 2,
				beneficiary: 6,
				valid_from: 1,
				expire_at: 6,
			}
			.into(),
		);
	});
}

#[test]
fn spend_expires() {
	new_test_ext().execute_with(|| {
		assert_eq!(<Test as Config>::PayoutPeriod::get(), 5);

		// spend `0` expires in 5 blocks after the creating.
		System::set_block_number(1);
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, None));
		System::set_block_number(6);
		assert_noop!(Treasury::payout(RuntimeOrigin::signed(1), 0), Error::<Test, _>::SpendExpired);

		// spend cannot be approved since its already expired.
		assert_noop!(
			Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, Some(0)),
			Error::<Test, _>::SpendExpired
		);
	});
}

#[docify::export]
#[test]
fn spend_payout_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		// approve a `2` coins spend of asset `1` to beneficiary `6`, the spend valid from now.
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, None));
		// payout the spend.
		assert_ok!(Treasury::payout(RuntimeOrigin::signed(1), 0));
		// beneficiary received `2` coins of asset `1`.
		assert_eq!(paid(6, 1), 2);
		assert_eq!(SpendCount::<Test, _>::get(), 1);
		let payment_id = get_payment_id(0).expect("no payment attempt");
		System::assert_last_event(Event::<Test, _>::Paid { index: 0, payment_id }.into());
		set_status(payment_id, PaymentStatus::Success);
		// the payment succeed.
		assert_ok!(Treasury::check_status(RuntimeOrigin::signed(1), 0));
		System::assert_last_event(Event::<Test, _>::SpendProcessed { index: 0 }.into());
		// cannot payout the same spend twice.
		assert_noop!(Treasury::payout(RuntimeOrigin::signed(1), 0), Error::<Test, _>::InvalidIndex);
	});
}

#[test]
fn payout_retry_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, None));
		assert_ok!(Treasury::payout(RuntimeOrigin::signed(1), 0));
		assert_eq!(paid(6, 1), 2);
		let payment_id = get_payment_id(0).expect("no payment attempt");
		// spend payment is failed
		set_status(payment_id, PaymentStatus::Failure);
		unpay(6, 1, 2);
		// cannot payout a spend in the attempted state
		assert_noop!(
			Treasury::payout(RuntimeOrigin::signed(1), 0),
			Error::<Test, _>::AlreadyAttempted
		);
		// check status and update it to retry the payout again
		assert_ok!(Treasury::check_status(RuntimeOrigin::signed(1), 0));
		System::assert_last_event(Event::<Test, _>::PaymentFailed { index: 0, payment_id }.into());
		// the payout can be retried now
		assert_ok!(Treasury::payout(RuntimeOrigin::signed(1), 0));
		assert_eq!(paid(6, 1), 2);
	});
}

#[test]
fn spend_valid_from_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(<Test as Config>::PayoutPeriod::get(), 5);
		System::set_block_number(1);

		// spend valid from block `2`.
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, Some(2)));
		assert_noop!(Treasury::payout(RuntimeOrigin::signed(1), 0), Error::<Test, _>::EarlyPayout);
		System::set_block_number(2);
		assert_ok!(Treasury::payout(RuntimeOrigin::signed(1), 0));

		System::set_block_number(5);
		// spend approved even if `valid_from` in the past since the payout period has not passed.
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, Some(4)));
		// spend paid.
		assert_ok!(Treasury::payout(RuntimeOrigin::signed(1), 1));
	});
}

#[test]
fn void_spend_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		// spend cannot be voided if already attempted.
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, Some(1)));
		assert_ok!(Treasury::payout(RuntimeOrigin::signed(1), 0));
		assert_noop!(
			Treasury::void_spend(RuntimeOrigin::root(), 0),
			Error::<Test, _>::AlreadyAttempted
		);

		// void spend.
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, Some(10)));
		assert_ok!(Treasury::void_spend(RuntimeOrigin::root(), 1));
		assert_eq!(Spends::<Test, _>::get(1), None);
	});
}

#[test]
fn check_status_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(<Test as Config>::PayoutPeriod::get(), 5);
		System::set_block_number(1);

		// spend `0` expired and can be removed.
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, None));
		System::set_block_number(7);
		let info = Treasury::check_status(RuntimeOrigin::signed(1), 0).unwrap();
		assert_eq!(info.pays_fee, Pays::No);
		System::assert_last_event(Event::<Test, _>::SpendProcessed { index: 0 }.into());

		// spend `1` payment failed and expired hence can be removed.
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, None));
		assert_noop!(
			Treasury::check_status(RuntimeOrigin::signed(1), 1),
			Error::<Test, _>::NotAttempted
		);
		assert_ok!(Treasury::payout(RuntimeOrigin::signed(1), 1));
		let payment_id = get_payment_id(1).expect("no payment attempt");
		set_status(payment_id, PaymentStatus::Failure);
		// spend expired.
		System::set_block_number(13);
		let info = Treasury::check_status(RuntimeOrigin::signed(1), 1).unwrap();
		assert_eq!(info.pays_fee, Pays::Yes);
		System::assert_last_event(Event::<Test, _>::PaymentFailed { index: 1, payment_id }.into());
		let info = Treasury::check_status(RuntimeOrigin::signed(1), 1).unwrap();
		assert_eq!(info.pays_fee, Pays::No);
		System::assert_last_event(Event::<Test, _>::SpendProcessed { index: 1 }.into());

		// spend `2` payment succeed.
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, None));
		assert_ok!(Treasury::payout(RuntimeOrigin::signed(1), 2));
		let payment_id = get_payment_id(2).expect("no payment attempt");
		set_status(payment_id, PaymentStatus::Success);
		let info = Treasury::check_status(RuntimeOrigin::signed(1), 2).unwrap();
		assert_eq!(info.pays_fee, Pays::No);
		System::assert_last_event(Event::<Test, _>::SpendProcessed { index: 2 }.into());

		// spend `3` payment in process.
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, None));
		assert_ok!(Treasury::payout(RuntimeOrigin::signed(1), 3));
		let payment_id = get_payment_id(3).expect("no payment attempt");
		set_status(payment_id, PaymentStatus::InProgress);
		assert_noop!(
			Treasury::check_status(RuntimeOrigin::signed(1), 3),
			Error::<Test, _>::Inconclusive
		);

		// spend `4` removed since the payment status is unknown.
		assert_ok!(Treasury::spend(RuntimeOrigin::signed(10), 1, 2, 6, None));
		assert_ok!(Treasury::payout(RuntimeOrigin::signed(1), 4));
		let payment_id = get_payment_id(4).expect("no payment attempt");
		set_status(payment_id, PaymentStatus::Unknown);
		let info = Treasury::check_status(RuntimeOrigin::signed(1), 4).unwrap();
		assert_eq!(info.pays_fee, Pays::No);
		System::assert_last_event(Event::<Test, _>::SpendProcessed { index: 4 }.into());
	});
}
