// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Refunder Module
//!
//! The Refunder module provides a means of buffer slashes before the treasury collects its reward.
//! It has a public function `slash` which takes the amount to be removed from the target's account
//! together with the target account, an identifier indicating the type of offence and some temporal
//! index specifying when the offence occurred. There is a second function `refund` which allows the
//! targets of a previous slash, as identified by the kind of offence and the index specifying when
//! the offence occurred, to be refunded in full. The configuration trait has a handler for when a
//! refund happens (as the staking module will require indication that the slash is returned for its
//! bookkeeping), as well as a period following the last target of a single offence after which the
//! funds may no longer be refunded. There is also an `OnUnbalanced` target for funds that are not
//! refunded, and an origin trait for where the `refund` call may come from.
//!
//! - [`refunder::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! The Refunder module is designed to sit between the Treasury and the Staking module, acting as a
//! buffer through which slashes go and retaining sufficient information on the slashes so that they
//! can be refunded should the governance system desire it.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! - `slash` - Reduce the balance of a target account by some amount in response to some offence.
//! - `refund` - Reverse the reductions in balance of a set of target accounts according to some
//!   offence.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use rstd::prelude::*;
use support::{decl_module, decl_storage, decl_event, ensure, print};
use support::traits::{
	Currency, ExistenceRequirement, Get, Imbalance, OnDilution, OnUnbalanced,
	ReservableCurrency, WithdrawReason
};
use sr_primitives::{Permill, Perbill, ModuleId};
use sr_primitives::traits::{
	Zero, EnsureOrigin, StaticLookup, AccountIdConversion, CheckedSub, Saturating
};
use sr_primitives::weights::SimpleDispatchInfo;
use codec::{Encode, Decode};
use system::ensure_signed;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
type PositiveImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;

const MODULE_ID: ModuleId = ModuleId(*b"py/refun");

pub trait Trait: system::Trait {
	/// The staking balance.
	type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

	/// Origin from which refund operations must come.
	type RefundOrigin: EnsureOrigin<Self::Origin>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// Handler for the unbalanced decrease when a slash eventually succeeds.
	type SlashSuccess: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Number of blocks after the last slash event that an offence may be refunded.
	type RefundPeriod: Get<Self::BlockNumber>;

	/// Number of blocks between successive attempts to check whether a refund period is up. Should
	/// be reasonably high (e.g. 600 or hourly on a 6-second chain) to reduce storage look-ups.
	type CheckPeriod: Get<Self::BlockNumber>;

	/// Handler for when a slash gets refunded.
	type Refunded: OnRefunded<Self::AccountId, BalanceOf<Self>>;

	/// The kinds of offences that can be reported.
	type OffenceKind: OffenceKind;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Period between successive spends.
		const RefundPeriod: T::BlockNumber = T::RefundPeriod::get();

		/// Number of blocks between successive attempts to check whether a refund period is up.
		const CheckPeriod: T::BlockNumber = T::CheckPeriod::get();

		fn deposit_event() = default;

		/// Refund a deposit to the origin offenders.
		///
		/// # <weight>
		/// - TODO
		/// # </weight>
		#[weight = SimpleDispatchInfo::FreeOperational]
		fn refund(origin,
			kind: OffenceKind,
			time_slot: OffenceTimeslot
		) {
			T::RefundOrigin::ensure_origin(origin)?;


		}

		fn on_initialize(n: T::BlockNumber) {
			// Check to see if we should spend some funds!
			if (n % T::SpendPeriod::get()).is_zero() {
				Self::spend_funds();
			}
		}
	}
}

/// A spending proposal.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq, sr_primitives::RuntimeDebug)]
pub struct Proposal<AccountId, Balance> {
	proposer: AccountId,
	value: Balance,
	beneficiary: AccountId,
	bond: Balance,
}

decl_storage! {
	trait Store for Module<T: Trait> as Treasury {
		/// Offence queue; all offences whose slashes are due to succeed in the given block.
		OffenceQueue: map T::BlockNumber => Vec<Offence>;
	}
}

decl_event!(
	pub enum Event<T>
	where
		Balance = BalanceOf<T>,
		<T as system::Trait>::AccountId
	{
		/// Someone got slashed.
		NewOffence(),
		/// New proposal.
		Completed(Balance),
		/// New proposal.
		Refunded(Balance),
		/// We have ended a spend period and will now allocate funds.
		Spending(Balance),
		/// Some funds have been allocated.
		Awarded(ProposalIndex, Balance, AccountId),
		/// Some of our funds have been burnt.
		Burnt(Balance),
		/// Spending has finished; this is the amount that rolls over until next spend.
		Rollover(Balance),
	}
);

impl<T: Trait> Module<T> {
	// Add public immutables and private mutables.

	/// The account ID of the treasury pot.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn account_id() -> T::AccountId {
		MODULE_ID.into_account()
	}

	/// Slash somebody
	fn slash(target: T::AccountId, amount: BalanceOf<T>, offence: ) {
		T::Currency::free_balance(&Self::account_id())
			// Must never be less than 0 but better be safe.
			.saturating_sub(T::Currency::minimum_balance())
	}
}

impl<T: Trait> OnUnbalanced<NegativeImbalanceOf<T>> for Module<T> {
	fn on_unbalanced(amount: NegativeImbalanceOf<T>) {
		// Must resolve into existing but better to be safe.
		let _ = T::Currency::resolve_creating(&Self::account_id(), amount);
	}
}

/// Mint extra funds for the treasury to keep the ratio of portion to total_issuance equal
/// pre dilution and post-dilution.
///
/// i.e.
/// ```nocompile
/// portion / total_issuance_before_dilution ==
///   (portion + minted) / (total_issuance_before_dilution + minted_to_treasury + minted)
/// ```
impl<T: Trait> OnDilution<BalanceOf<T>> for Module<T> {
	fn on_dilution(minted: BalanceOf<T>, portion: BalanceOf<T>) {
		if !minted.is_zero() && !portion.is_zero() {
			let total_issuance = T::Currency::total_issuance();
			if let Some(funding) = total_issuance.checked_sub(&portion) {
				let increase_ratio = Perbill::from_rational_approximation(minted, portion);
				let funding = increase_ratio * funding;
				Self::on_unbalanced(T::Currency::issue(funding));
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use support::{assert_noop, assert_ok, impl_outer_origin, parameter_types};
	use primitives::H256;
	use sr_primitives::{
		traits::{BlakeTwo256, OnFinalize, IdentityLookup}, testing::Header, assert_eq_error_rate,
	};

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: u32 = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = ();
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
		pub const TransferFee: u64 = 0;
		pub const CreationFee: u64 = 0;
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type OnNewAccount = ();
		type OnFreeBalanceZero = ();
		type Event = ();
		type TransferPayment = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type TransferFee = TransferFee;
		type CreationFee = CreationFee;
	}
	parameter_types! {
		pub const ProposalBond: Permill = Permill::from_percent(5);
		pub const ProposalBondMinimum: u64 = 1;
		pub const SpendPeriod: u64 = 2;
		pub const Burn: Permill = Permill::from_percent(50);
	}
	impl Trait for Test {
		type Currency = balances::Module<Test>;
		type ApproveOrigin = system::EnsureRoot<u64>;
		type RejectOrigin = system::EnsureRoot<u64>;
		type Event = ();
		type ProposalRejection = ();
		type ProposalBond = ProposalBond;
		type ProposalBondMinimum = ProposalBondMinimum;
		type SpendPeriod = SpendPeriod;
		type Burn = Burn;
	}
	type Balances = balances::Module<Test>;
	type Treasury = Module<Test>;

	fn new_test_ext() -> runtime_io::TestExternalities {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		balances::GenesisConfig::<Test>{
			// Total issuance will be 200 with treasury account initialized at ED.
			balances: vec![(0, 100), (1, 98), (2, 1)],
			vesting: vec![],
		}.assimilate_storage(&mut t).unwrap();
		GenesisConfig::default().assimilate_storage::<Test>(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn genesis_config_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(Treasury::pot(), 0);
			assert_eq!(Treasury::proposal_count(), 0);
		});
	}

	#[test]
	fn minting_works() {
		new_test_ext().execute_with(|| {
			// Check that accumulate works when we have Some value in Dummy already.
			Treasury::on_dilution(100, 100);
			assert_eq!(Treasury::pot(), 100);
		});
	}

	#[test]
	fn minting_works_2() {
		let tests = [(1, 10), (1, 20), (40, 130), (2, 66), (2, 67), (2, 100), (2, 101), (2, 134)];
		for &(minted, portion) in &tests {
			new_test_ext().execute_with(|| {
				let init_total_issuance = Balances::total_issuance();
				Treasury::on_dilution(minted, portion);

				assert_eq!(
					Treasury::pot(),
					(((init_total_issuance - portion) * minted) as f32 / portion as f32)
						.round() as u64
				);

				// Assert:
				// portion / init_total_issuance
				// == (portion + minted) / (init_total_issuance + Treasury::pot() + minted),
				assert_eq_error_rate!(
					portion * 1_000 / init_total_issuance,
					(portion + minted) * 1_000 / (init_total_issuance + Treasury::pot() + minted),
					2,
				);
			});
		}
	}

	#[test]
	fn spend_proposal_takes_min_deposit() {
		new_test_ext().execute_with(|| {
			assert_ok!(Treasury::propose_spend(Origin::signed(0), 1, 3));
			assert_eq!(Balances::free_balance(&0), 99);
			assert_eq!(Balances::reserved_balance(&0), 1);
		});
	}

	#[test]
	fn spend_proposal_takes_proportional_deposit() {
		new_test_ext().execute_with(|| {
			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_eq!(Balances::free_balance(&0), 95);
			assert_eq!(Balances::reserved_balance(&0), 5);
		});
	}

	#[test]
	fn spend_proposal_fails_when_proposer_poor() {
		new_test_ext().execute_with(|| {
			assert_noop!(Treasury::propose_spend(Origin::signed(2), 100, 3), "Proposer's balance too low");
		});
	}

	#[test]
	fn accepted_spend_proposal_ignored_outside_spend_period() {
		new_test_ext().execute_with(|| {
			Treasury::on_dilution(100, 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(1);
			assert_eq!(Balances::free_balance(&3), 0);
			assert_eq!(Treasury::pot(), 100);
		});
	}

	#[test]
	fn unused_pot_should_diminish() {
		new_test_ext().execute_with(|| {
			let init_total_issuance = Balances::total_issuance();
			Treasury::on_dilution(100, 100);
			assert_eq!(Balances::total_issuance(), init_total_issuance + 100);

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Treasury::pot(), 50);
			assert_eq!(Balances::total_issuance(), init_total_issuance + 50);
		});
	}

	#[test]
	fn rejected_spend_proposal_ignored_on_spend_period() {
		new_test_ext().execute_with(|| {
			Treasury::on_dilution(100, 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::reject_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Balances::free_balance(&3), 0);
			assert_eq!(Treasury::pot(), 50);
		});
	}

	#[test]
	fn reject_already_rejected_spend_proposal_fails() {
		new_test_ext().execute_with(|| {
			Treasury::on_dilution(100, 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::reject_proposal(Origin::ROOT, 0));
			assert_noop!(Treasury::reject_proposal(Origin::ROOT, 0), "No proposal at that index");
		});
	}

	#[test]
	fn reject_non_existant_spend_proposal_fails() {
		new_test_ext().execute_with(|| {
			assert_noop!(Treasury::reject_proposal(Origin::ROOT, 0), "No proposal at that index");
		});
	}

	#[test]
	fn accept_non_existant_spend_proposal_fails() {
		new_test_ext().execute_with(|| {
			assert_noop!(Treasury::approve_proposal(Origin::ROOT, 0), "No proposal at that index");
		});
	}

	#[test]
	fn accept_already_rejected_spend_proposal_fails() {
		new_test_ext().execute_with(|| {
			Treasury::on_dilution(100, 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::reject_proposal(Origin::ROOT, 0));
			assert_noop!(Treasury::approve_proposal(Origin::ROOT, 0), "No proposal at that index");
		});
	}

	#[test]
	fn accepted_spend_proposal_enacted_on_spend_period() {
		new_test_ext().execute_with(|| {
			Treasury::on_dilution(100, 100);
			assert_eq!(Treasury::pot(), 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Balances::free_balance(&3), 100);
			assert_eq!(Treasury::pot(), 0);
		});
	}

	#[test]
	fn pot_underflow_should_not_diminish() {
		new_test_ext().execute_with(|| {
			Treasury::on_dilution(100, 100);
			assert_eq!(Treasury::pot(), 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 150, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Treasury::pot(), 100); // Pot hasn't changed

			Treasury::on_dilution(100, 100);
			<Treasury as OnFinalize<u64>>::on_finalize(4);
			assert_eq!(Balances::free_balance(&3), 150); // Fund has been spent
			assert_eq!(Treasury::pot(), 75); // Pot has finally changed
		});
	}

	// Treasury account doesn't get deleted if amount approved to spend is all its free balance.
	// i.e. pot should not include existential deposit needed for account survival.
	#[test]
	fn treasury_account_doesnt_get_deleted() {
		new_test_ext().execute_with(|| {
			Treasury::on_dilution(100, 100);
			assert_eq!(Treasury::pot(), 100);
			let treasury_balance = Balances::free_balance(&Treasury::account_id());

			assert_ok!(Treasury::propose_spend(Origin::signed(0), treasury_balance, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Treasury::pot(), 100); // Pot hasn't changed

			assert_ok!(Treasury::propose_spend(Origin::signed(0), Treasury::pot(), 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 1));

			<Treasury as OnFinalize<u64>>::on_finalize(4);
			assert_eq!(Treasury::pot(), 0); // Pot is emptied
			assert_eq!(Balances::free_balance(&Treasury::account_id()), 1); // but the account is still there
		});
	}

	// In case treasury account is not existing then it works fine.
	// This is usefull for chain that will just update runtime.
	#[test]
	fn inexisting_account_works() {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		balances::GenesisConfig::<Test>{
			balances: vec![(0, 100), (1, 99), (2, 1)],
			vesting: vec![],
		}.assimilate_storage(&mut t).unwrap();
		// Treasury genesis config is not build thus treasury account does not exist
		let mut t: runtime_io::TestExternalities = t.into();

		t.execute_with(|| {
			assert_eq!(Balances::free_balance(&Treasury::account_id()), 0); // Account does not exist
			assert_eq!(Treasury::pot(), 0); // Pot is empty

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 99, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));
			assert_ok!(Treasury::propose_spend(Origin::signed(0), 1, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 1));
			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Treasury::pot(), 0); // Pot hasn't changed
			assert_eq!(Balances::free_balance(&3), 0); // Balance of `3` hasn't changed

			Treasury::on_dilution(100, 100);
			assert_eq!(Treasury::pot(), 99); // Pot now contains funds
			assert_eq!(Balances::free_balance(&Treasury::account_id()), 100); // Account does exist

			<Treasury as OnFinalize<u64>>::on_finalize(4);

			assert_eq!(Treasury::pot(), 0); // Pot has changed
			assert_eq!(Balances::free_balance(&3), 99); // Balance of `3` has changed
		});
	}
}
