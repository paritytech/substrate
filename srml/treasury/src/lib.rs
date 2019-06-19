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

//! # Treasury Module
//!
//! The Treasury module provides a "pot" of funds that can be managed by stakeholders in the
//! system and a structure for making spending proposals from this pot.
//!
//! - [`treasury::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! The Treasury Module itself provides the pot to store funds, and a means for stakeholders to
//! propose, approve, and deny expendatures.  The chain will need to provide a method (e.g.
//! inflation, fees) for collecting funds.
//!
//! By way of example, the Council could vote to fund the Treasury with a portion of the block
//! reward and use the funds to pay developers.
//!
//! ### Terminology
//!
//! - **Proposal:** A suggestion to allocate funds from the pot to a beneficiary.
//! - **Beneficiary:** An account who will receive the funds from a proposal iff
//! the proposal is approved.
//! - **Deposit:** Funds that a proposer must lock when making a proposal. The
//! deposit will be returned or slashed if the proposal is approved or rejected
//! respectively.
//! - **Pot:** Unspent funds accumulated by the treasury module.
//!
//! ### Implementations
//!
//! The treasury module provides an implementation for the following trait:
//!
//! - `OnDilution` - When new funds are minted to reward the deployment of other existing funds,
//! a corresponding amount of tokens are minted into the treasury so that the tokens being rewarded
//! do not represent a higher portion of total supply. For example, in the default substrate node,
//! when validators are rewarded new tokens for staking, they do not hold a higher portion of total
//! tokens. Rather, tokens are added to the treasury to keep the portion of tokens staked constant.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! - `propose_spend` - Make a spending proposal and stake the required deposit.
//! - `set_pot` - Set the spendable balance of funds.
//! - `configure` - Configure the module's proposal requirements.
//! - `reject_proposal` - Reject a proposal, slashing the deposit.
//! - `approve_proposal` - Accept the proposal, returning the deposit.
//!
//! ## GenesisConfig
//!
//! The Treasury module depends on the [`GenesisConfig`](./struct.GenesisConfig.html).

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use rstd::prelude::*;
use srml_support::{StorageValue, StorageMap, decl_module, decl_storage, decl_event, ensure};
use srml_support::traits::{Currency, ReservableCurrency, OnDilution, OnUnbalanced, Imbalance};
use runtime_primitives::{Permill,
	traits::{Zero, EnsureOrigin, StaticLookup, Saturating, CheckedSub, CheckedMul}
};
use parity_codec::{Encode, Decode};
use system::ensure_signed;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
type PositiveImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;

pub trait Trait: system::Trait {
	/// The staking balance.
	type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

	/// Origin from which approvals must come.
	type ApproveOrigin: EnsureOrigin<Self::Origin>;

	/// Origin from which rejections must come.
	type RejectOrigin: EnsureOrigin<Self::Origin>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// Handler for the unbalanced increase when minting cash from the "Pot".
	type MintedForSpending: OnUnbalanced<PositiveImbalanceOf<Self>>;

	/// Handler for the unbalanced decrease when slashing for a rejected proposal.
	type ProposalRejection: OnUnbalanced<NegativeImbalanceOf<Self>>;
}

type ProposalIndex = u32;

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;
		/// Put forward a suggestion for spending. A deposit proportional to the value
		/// is reserved and slashed if the proposal is rejected. It is returned once the
		/// proposal is awarded.
		///
		/// # <weight>
		/// - O(1).
		/// - Limited storage reads.
		/// - One DB change, one extra DB entry.
		/// # </weight>
		fn propose_spend(
			origin,
			#[compact] value: BalanceOf<T>,
			beneficiary: <T::Lookup as StaticLookup>::Source
		) {
			let proposer = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			let bond = Self::calculate_bond(value);
			T::Currency::reserve(&proposer, bond)
				.map_err(|_| "Proposer's balance too low")?;

			let c = Self::proposal_count();
			<ProposalCount<T>>::put(c + 1);
			<Proposals<T>>::insert(c, Proposal { proposer, value, beneficiary, bond });

			Self::deposit_event(RawEvent::Proposed(c));
		}

		/// Set the balance of funds available to spend.
		fn set_pot(#[compact] new_pot: BalanceOf<T>) {
			// Put the new value into storage.
			<Pot<T>>::put(new_pot);
		}

		/// (Re-)configure this module.
		fn configure(
			#[compact] proposal_bond: Permill,
			#[compact] proposal_bond_minimum: BalanceOf<T>,
			#[compact] spend_period: T::BlockNumber,
			#[compact] burn: Permill
		) {
			<ProposalBond<T>>::put(proposal_bond);
			<ProposalBondMinimum<T>>::put(proposal_bond_minimum);
			<SpendPeriod<T>>::put(spend_period);
			<Burn<T>>::put(burn);
		}

		/// Reject a proposed spend. The original deposit will be slashed.
		///
		/// # <weight>
		/// - O(1).
		/// - Limited storage reads.
		/// - One DB clear.
		/// # </weight>
		fn reject_proposal(origin, #[compact] proposal_id: ProposalIndex) {
			T::RejectOrigin::ensure_origin(origin)?;
			let proposal = <Proposals<T>>::take(proposal_id).ok_or("No proposal at that index")?;

			let value = proposal.bond;
			let imbalance = T::Currency::slash_reserved(&proposal.proposer, value).0;
			T::ProposalRejection::on_unbalanced(imbalance);
		}

		/// Approve a proposal. At a later time, the proposal will be allocated to the beneficiary
		/// and the original deposit will be returned.
		///
		/// # <weight>
		/// - O(1).
		/// - Limited storage reads.
		/// - One DB change.
		/// # </weight>
		fn approve_proposal(origin, #[compact] proposal_id: ProposalIndex) {
			T::ApproveOrigin::ensure_origin(origin)?;

			ensure!(<Proposals<T>>::exists(proposal_id), "No proposal at that index");

			<Approvals<T>>::mutate(|v| v.push(proposal_id));
		}

		fn on_finalize(n: T::BlockNumber) {
			// Check to see if we should spend some funds!
			if (n % Self::spend_period()).is_zero() {
				Self::spend_funds();
			}
		}
	}
}

/// A spending proposal.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
pub struct Proposal<AccountId, Balance> {
	proposer: AccountId,
	value: Balance,
	beneficiary: AccountId,
	bond: Balance,
}

decl_storage! {
	trait Store for Module<T: Trait> as Treasury {
		// Config...

		/// Fraction of a proposal's value that should be bonded in order to place the proposal.
		/// An accepted proposal gets these back. A rejected proposal does not.
		ProposalBond get(proposal_bond) config(): Permill;

		/// Minimum amount of funds that should be placed in a deposit for making a proposal.
		ProposalBondMinimum get(proposal_bond_minimum) config(): BalanceOf<T>;

		/// Period between successive spends.
		SpendPeriod get(spend_period) config(): T::BlockNumber = runtime_primitives::traits::One::one();

		/// Percentage of spare funds (if any) that are burnt per spend period.
		Burn get(burn) config(): Permill;

		// State...

		/// Total funds available to this module for spending.
		Pot get(pot): BalanceOf<T>;

		/// Number of proposals that have been made.
		ProposalCount get(proposal_count): ProposalIndex;

		/// Proposals that have been made.
		Proposals get(proposals): map ProposalIndex => Option<Proposal<T::AccountId, BalanceOf<T>>>;

		/// Proposal indices that have been approved but not yet awarded.
		Approvals get(approvals): Vec<ProposalIndex>;
	}
}

decl_event!(
	pub enum Event<T>
	where
		Balance = BalanceOf<T>,
		<T as system::Trait>::AccountId
	{
		/// New proposal.
		Proposed(ProposalIndex),
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

	/// The needed bond for a proposal whose spend is `value`.
	fn calculate_bond(value: BalanceOf<T>) -> BalanceOf<T> {
		Self::proposal_bond_minimum().max(Self::proposal_bond() * value)
	}

	// Spend some money!
	fn spend_funds() {
		let mut budget_remaining = Self::pot();
		Self::deposit_event(RawEvent::Spending(budget_remaining));

		let mut missed_any = false;
		let mut imbalance = <PositiveImbalanceOf<T>>::zero();
		<Approvals<T>>::mutate(|v| {
			v.retain(|&index| {
				// Should always be true, but shouldn't panic if false or we're screwed.
				if let Some(p) = Self::proposals(index) {
					if p.value <= budget_remaining {
						budget_remaining -= p.value;
						<Proposals<T>>::remove(index);

						// return their deposit.
						let _ = T::Currency::unreserve(&p.proposer, p.bond);

						// provide the allocation.
						imbalance.subsume(T::Currency::deposit_creating(&p.beneficiary, p.value));

						Self::deposit_event(RawEvent::Awarded(index, p.value, p.beneficiary));
						false
					} else {
						missed_any = true;
						true
					}
				} else {
					false
				}
			});
		});

		T::MintedForSpending::on_unbalanced(imbalance);

		if !missed_any {
			// burn some proportion of the remaining budget if we run a surplus.
			let burn = (Self::burn() * budget_remaining).min(budget_remaining);
			budget_remaining -= burn;
			Self::deposit_event(RawEvent::Burnt(burn))
		}

		Self::deposit_event(RawEvent::Rollover(budget_remaining));

		<Pot<T>>::put(budget_remaining);
	}
}

impl<T: Trait> OnDilution<BalanceOf<T>> for Module<T> {
	fn on_dilution(minted: BalanceOf<T>, portion: BalanceOf<T>) {
		// Mint extra funds for the treasury to keep the ratio of portion to total_issuance equal
		// pre dilution and post-dilution.
		if !minted.is_zero() && !portion.is_zero() {
			let total_issuance = T::Currency::total_issuance();
			if let Some(funding) = total_issuance.checked_sub(&portion) {
				let funding = funding / portion;
				if let Some(funding) = funding.checked_mul(&minted) {
					<Pot<T>>::mutate(|x| *x = x.saturating_add(funding));
				}
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use runtime_io::with_externalities;
	use srml_support::{impl_outer_origin, assert_ok, assert_noop};
	use substrate_primitives::{H256, Blake2Hasher};
	use runtime_primitives::BuildStorage;
	use runtime_primitives::traits::{BlakeTwo256, OnFinalize, IdentityLookup};
	use runtime_primitives::testing::Header;

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type OnNewAccount = ();
		type OnFreeBalanceZero = ();
		type Event = ();
		type TransactionPayment = ();
		type TransferPayment = ();
		type DustRemoval = ();
	}
	impl Trait for Test {
		type Currency = balances::Module<Test>;
		type ApproveOrigin = system::EnsureRoot<u64>;
		type RejectOrigin = system::EnsureRoot<u64>;
		type Event = ();
		type MintedForSpending = ();
		type ProposalRejection = ();
	}
	type Balances = balances::Module<Test>;
	type Treasury = Module<Test>;

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap().0;
		t.extend(balances::GenesisConfig::<Test>{
			balances: vec![(0, 100), (1, 99), (2, 1)],
			transaction_base_fee: 0,
			transaction_byte_fee: 0,
			transfer_fee: 0,
			creation_fee: 0,
			existential_deposit: 0,
			vesting: vec![],
		}.build_storage().unwrap().0);
		t.extend(GenesisConfig::<Test>{
			proposal_bond: Permill::from_percent(5),
			proposal_bond_minimum: 1,
			spend_period: 2,
			burn: Permill::from_percent(50),
		}.build_storage().unwrap().0);
		t.into()
	}

	#[test]
	fn genesis_config_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Treasury::proposal_bond(), Permill::from_percent(5));
			assert_eq!(Treasury::proposal_bond_minimum(), 1);
			assert_eq!(Treasury::spend_period(), 2);
			assert_eq!(Treasury::burn(), Permill::from_percent(50));
			assert_eq!(Treasury::pot(), 0);
			assert_eq!(Treasury::proposal_count(), 0);
		});
	}

	#[test]
	fn minting_works() {
		with_externalities(&mut new_test_ext(), || {
			// Check that accumulate works when we have Some value in Dummy already.
			Treasury::on_dilution(100, 100);
			assert_eq!(Treasury::pot(), 100);
		});
	}

	#[test]
	fn spend_proposal_takes_min_deposit() {
		with_externalities(&mut new_test_ext(), || {
			assert_ok!(Treasury::propose_spend(Origin::signed(0), 1, 3));
			assert_eq!(Balances::free_balance(&0), 99);
			assert_eq!(Balances::reserved_balance(&0), 1);
		});
	}

	#[test]
	fn spend_proposal_takes_proportional_deposit() {
		with_externalities(&mut new_test_ext(), || {
			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_eq!(Balances::free_balance(&0), 95);
			assert_eq!(Balances::reserved_balance(&0), 5);
		});
	}

	#[test]
	fn spend_proposal_fails_when_proposer_poor() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Treasury::propose_spend(Origin::signed(2), 100, 3), "Proposer's balance too low");
		});
	}

	#[test]
	fn accepted_spend_proposal_ignored_outside_spend_period() {
		with_externalities(&mut new_test_ext(), || {
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
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_dilution(100, 100);

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Treasury::pot(), 50);
		});
	}

	#[test]
	fn rejected_spend_proposal_ignored_on_spend_period() {
		with_externalities(&mut new_test_ext(), || {
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
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_dilution(100, 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::reject_proposal(Origin::ROOT, 0));
			assert_noop!(Treasury::reject_proposal(Origin::ROOT, 0), "No proposal at that index");
		});
	}

	#[test]
	fn reject_non_existant_spend_proposal_fails() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Treasury::reject_proposal(Origin::ROOT, 0), "No proposal at that index");
		});
	}

	#[test]
	fn accept_non_existant_spend_proposal_fails() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Treasury::approve_proposal(Origin::ROOT, 0), "No proposal at that index");
		});
	}

	#[test]
	fn accept_already_rejected_spend_proposal_fails() {
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_dilution(100, 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::reject_proposal(Origin::ROOT, 0));
			assert_noop!(Treasury::approve_proposal(Origin::ROOT, 0), "No proposal at that index");
		});
	}

	#[test]
	fn accepted_spend_proposal_enacted_on_spend_period() {
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_dilution(100, 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Balances::free_balance(&3), 100);
			assert_eq!(Treasury::pot(), 0);
		});
	}

	#[test]
	// Note: This test demonstrates that `on_dilution` does not increase the pot with good resolution
	// with large amounts of the network staked. https://github.com/paritytech/substrate/issues/2579
	// A fix to 2579 should include a change of this test.
	fn on_dilution_quantization_effects() {
		with_externalities(&mut new_test_ext(), || {
			// minted = 1% of total issuance for all cases
			let _ = Treasury::set_pot(0);
			assert_eq!(Balances::total_issuance(), 200);

			Treasury::on_dilution(2, 66);   // portion = 33% of total issuance
			assert_eq!(Treasury::pot(), 4); // should increase by 4 (200 - 66) / 66 * 2

			Treasury::on_dilution(2, 67);   // portion = 33+eps% of total issuance
			assert_eq!(Treasury::pot(), 6); // should increase by 2 (200 - 67) / 67 * 2

			Treasury::on_dilution(2, 100);  // portion = 50% of total issuance
			assert_eq!(Treasury::pot(), 8); // should increase by 2 (200 - 100) / 100 * 2

			// If any more than 50% of the network is staked (i.e. (2 * portion) > total_issuance)
			// then the pot will not increase.
			Treasury::on_dilution(2, 101);  // portion = 50+eps% of total issuance
			assert_eq!(Treasury::pot(), 8); // should increase by 0 (200 - 101) / 101 * 2

			Treasury::on_dilution(2, 134);  // portion = 67% of total issuance
			assert_eq!(Treasury::pot(), 8); // should increase by 0 (200 - 134) / 134 * 2
		});
	}

	#[test]
	fn pot_underflow_should_not_diminish() {
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_dilution(100, 100);

			assert_ok!(Treasury::propose_spend(Origin::signed(0), 150, 3));
			assert_ok!(Treasury::approve_proposal(Origin::ROOT, 0));

			<Treasury as OnFinalize<u64>>::on_finalize(2);
			assert_eq!(Treasury::pot(), 100);

			Treasury::on_dilution(100, 100);
			<Treasury as OnFinalize<u64>>::on_finalize(4);
			assert_eq!(Balances::free_balance(&3), 150);
			assert_eq!(Treasury::pot(), 25);
		});
	}
}
