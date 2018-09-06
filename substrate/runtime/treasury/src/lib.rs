// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! The Treasury: Keeps account of the taxed cash and handles its deployment.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg_attr(any(feature = "std", test), macro_use)]
extern crate substrate_runtime_std as rstd;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

#[cfg(any(feature = "std", test))]
extern crate substrate_runtime_io as runtime_io;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate substrate_codec_derive;

extern crate substrate_codec as codec;
#[cfg(test)]
extern crate substrate_primitives;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_runtime_system as system;
extern crate substrate_runtime_balances as balances;

use rstd::ops::{Mul, Div};
use runtime_support::{StorageValue, StorageMap};
use runtime_support::dispatch::Result;
use runtime_primitives::traits::{As, OnFinalise, Zero, RefInto};
use balances::OnMinted;

/// Our module's configuration trait. All our types and consts go in here. If the
/// module is dependent on specific other modules, then their configuration traits
/// should be added to our implied traits list.
/// 
/// `system::Trait` should always be included in our implied traits.
pub trait Trait: balances::Trait {
	/// The overarching event type. 
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

type ProposalIndex = u32;

// The module declaration. This states the entry points that we handle. The
// macro takes care of the marshalling of arguments and dispatch.
decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait>;

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: T::PublicAux {
		// Put forward a suggestion for spending. A deposit proportional to the value
		// is reserved and slashed if the proposal is rejected. It is returned once the
		// proposal is awarded.
		fn propose_spend(aux, value: T::Balance, beneficiary: T::AccountId) -> Result;
	}

	// The priviledged entry points. These are provided to allow any governance modules in 
	// the runtime to be able to execute common functions. Unlike for `Call` there is no
	// auxilliary data to encode the sender (since there is no sender). Though still important
	// to ensure that these execute in reasonable time and space, they can do what would
	// otherwise be costly or unsafe operations.
	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum PrivCall {
		// Set the balance of funds available to spend.
		fn set_pot(new_pot: T::Balance) -> Result;

		// (Re-)configure this module.
		fn configure(proposal_bond: Permill, proposal_bond_minimum: T::Balance, spend_period: T::BlockNumber, burn: Permill) -> Result;

		// Reject a proposed spend. The original deposit will be slashed.
		fn reject_proposal(proposal_id: ProposalIndex) -> Result;

		// Approve a proposal. At a later time, the proposal will be allocated to the beneficiary
		// and the original deposit will be returned.
		fn approve_proposal(proposal_id: ProposalIndex) -> Result;
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

/// Permill is parts-per-million (i.e. after multiplying by this, divide by `PERMILL`).
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, Default, Copy, Clone, PartialEq, Eq)]
pub struct Permill(u32);

// TODO: impl Mul<Permill> for N where N: As<usize>
impl Permill {
	fn times<N: As<usize> + Mul<N, Output=N> + Div<N, Output=N>>(self, b: N) -> N {
		// TODO: handle overflows
		b * <N as As<usize>>::sa(self.0 as usize) / <N as As<usize>>::sa(1000000)
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Treasury {
		// Config...

		/// Proportion of funds that should be bonded in order to place a proposal. An accepted
		/// proposal gets these back. A rejected proposal doesn't.
		ProposalBond get(proposal_bond): required Permill;
		
		/// Minimum amount of funds that should be placed ina deposit for making a proposal.
		ProposalBondMinimum get(proposal_bond_minimum): required T::Balance;

		/// Period between successive spends.
		SpendPeriod get(spend_period): required T::BlockNumber;

		/// Percentage of spare funds (if any) that are burnt per spend period.
		Burn get(burn): required Permill;

		// State...

		/// Total funds available to this module for spending.
		Pot get(pot): default T::Balance;

		/// Number of proposals that have been made.
		ProposalCount get(proposal_count): default ProposalIndex;

		/// Proposals that have been made.
		Proposals get(proposals): map [ ProposalIndex => Proposal<T::AccountId, T::Balance> ];

		/// Proposal indices that have been approved but not yet awarded.
		Approvals get(approvals): default Vec<ProposalIndex>;
	}
}

/// Exported Event type that's generic over the configuration trait.
pub type Event<T> = RawEvent<
	<T as balances::Trait>::Balance,
	<T as system::Trait>::AccountId,
>;

/// An event in this module.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawEvent<Balance, AccountId> {
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

impl<B, A> From<RawEvent<B, A>> for () {
	fn from(_: RawEvent<B, A>) -> () { () }
}

impl<T: Trait> Module<T> {
	/// Deposit one of this module's events.
	fn deposit_event(event: Event<T>) {
		<system::Module<T>>::deposit_event(<T as Trait>::Event::from(event).into());
	}

	// Implement Calls/PrivCalls and add public immutables and private mutables.

	fn propose_spend(aux: &T::PublicAux, value: T::Balance, beneficiary: T::AccountId) -> Result {
		let proposer = aux.ref_into();

		let bond = Self::calculate_bond(value);
		<balances::Module<T>>::reserve(proposer, bond)
			.map_err(|_| "Proposer's balance too low")?;

		let c = Self::proposal_count();
		<ProposalCount<T>>::put(c + 1);
		<Proposals<T>>::insert(c, Proposal { proposer: proposer.clone(), value, beneficiary, bond });

		Self::deposit_event(RawEvent::Proposed(c));

		Ok(())
	}

	fn reject_proposal(proposal_id: ProposalIndex) -> Result {
		let proposal = <Proposals<T>>::take(proposal_id).ok_or("No proposal at that index")?;
		
		let value = proposal.bond;
		let _ = <balances::Module<T>>::slash_reserved(&proposal.proposer, value);

		Ok(())
	}

	fn approve_proposal(proposal_id: ProposalIndex) -> Result {
		ensure!(<Proposals<T>>::exists(proposal_id), "No proposal at that index");

		{
			let mut v = <Approvals<T>>::get();
			v.push(proposal_id);
			<Approvals<T>>::put(v);
		}
		//TODO gav: make work:
		//<Approvals<T>>::mutate(|a| a.push(proposal_id));

		Ok(())
	}

	fn set_pot(new_pot: T::Balance) -> Result {
		// Put the new value into storage.
		<Pot<T>>::put(new_pot);

		// All good.
		Ok(())
	}

	fn configure(
		proposal_bond: Permill,
		proposal_bond_minimum: T::Balance,
		spend_period: T::BlockNumber,
		burn: Permill
	) -> Result {
		<ProposalBond<T>>::put(proposal_bond);
		<ProposalBondMinimum<T>>::put(proposal_bond_minimum);
		<SpendPeriod<T>>::put(spend_period);
		<Burn<T>>::put(burn);
		Ok(())
	}

	/// The needed bond for a proposal whose spend is `value`.
	fn calculate_bond(value: T::Balance) -> T::Balance {
		Self::proposal_bond_minimum().max(Self::proposal_bond().times(value))
	}

	// Spend some money!
	fn spend_funds() {
		let mut budget_remaining = Self::pot();
		Self::deposit_event(RawEvent::Spending(budget_remaining));

		let mut missed_any = false;
		let remaining_approvals: Vec<_> = <Approvals<T>>::get().into_iter().filter(|&index| {
			// Should always be true, but shouldn't panic if false or we're screwed.
			if let Some(p) = Self::proposals(index) {
				if p.value <= budget_remaining {
					budget_remaining -= p.value;
					<Proposals<T>>::remove(index);

					// return their deposit.
					let _ = <balances::Module<T>>::unreserve(&p.proposer, p.bond);

					// provide the allocation.
					<balances::Module<T>>::increase_free_balance_creating(&p.beneficiary, p.value);

					Self::deposit_event(RawEvent::Awarded(index, p.value, p.beneficiary));
					false
				} else {
					missed_any = true;
					true
				}
			} else {
				false	
			}
		}).collect();
		<Approvals<T>>::put(remaining_approvals);

		if !missed_any {
			// burn some proportion of the remaining budget if we run a surplus.
			let burn = Self::burn().times(budget_remaining);
			budget_remaining -= burn;
			Self::deposit_event(RawEvent::Burnt(burn))
		}

		Self::deposit_event(RawEvent::Rollover(budget_remaining));

		<Pot<T>>::put(budget_remaining);
	}
}

impl<T: Trait> OnMinted<T::Balance> for Module<T> {
	fn on_minted(b: T::Balance) {
		<Pot<T>>::put(Self::pot() + b);
	}
}

impl<T: Trait> OnFinalise<T::BlockNumber> for Module<T> {
	fn on_finalise(n: T::BlockNumber) {
		// Check to see if we should spend some funds!
		if (n % Self::spend_period()).is_zero() {
			Self::spend_funds();
		}
	}
}

#[cfg(any(feature = "std", test))]
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
/// The genesis block configuration type. This is a simple default-capable struct that
/// contains any fields with which this module can be configured at genesis time.
pub struct GenesisConfig<T: Trait> {
	pub proposal_bond: Permill,
	pub proposal_bond_minimum: T::Balance,
	pub spend_period: T::BlockNumber,
	pub burn: Permill,
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig {
			proposal_bond: Default::default(),
			proposal_bond_minimum: Default::default(),
			spend_period: Default::default(),
			burn: Default::default(),
		}
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> runtime_primitives::BuildStorage for GenesisConfig<T>
{
	fn build_storage(self) -> ::std::result::Result<runtime_primitives::StorageMap, String> {
		use codec::Encode;
		Ok(map![
			Self::hash(<ProposalBond<T>>::key()).to_vec() => self.proposal_bond.encode(),
			Self::hash(<ProposalBondMinimum<T>>::key()).to_vec() => self.proposal_bond_minimum.encode(),
			Self::hash(<SpendPeriod<T>>::key()).to_vec() => self.spend_period.encode(),
			Self::hash(<Burn<T>>::key()).to_vec() => self.burn.encode()
		])
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use runtime_io::with_externalities;
	use substrate_primitives::{H256, KeccakHasher};
	use runtime_primitives::BuildStorage;
	use runtime_primitives::traits::{BlakeTwo256};
	use runtime_primitives::testing::{Digest, Header};

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl system::Trait for Test {
		type PublicAux = Self::AccountId;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
		type Event = ();
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type AccountIndex = u64;
		type OnFreeBalanceZero = ();
		type EnsureAccountLiquid = ();
		type Event = ();
	}
	impl Trait for Test {
		type Event = ();
	}
	type Balances = balances::Module<Test>;
	type Treasury = Module<Test>;

	fn new_test_ext() -> runtime_io::TestExternalities<KeccakHasher> {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
		t.extend(balances::GenesisConfig::<Test>{
			balances: vec![(0, 100), (1, 10), (2, 1)],
			transaction_base_fee: 0,
			transaction_byte_fee: 0,
			transfer_fee: 0,
			creation_fee: 0,
			existential_deposit: 0,
			reclaim_rebate: 0,
		}.build_storage().unwrap());
		t.extend(GenesisConfig::<Test>{
			proposal_bond: Permill(50_000),	// 5%
			proposal_bond_minimum: 1,
			spend_period: 2,
			burn: Permill(500_000),			// 50%
		}.build_storage().unwrap());
		t.into()
	}

	#[test]
	fn genesis_config_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Treasury::proposal_bond(), Permill(50_000));
			assert_eq!(Treasury::proposal_bond_minimum(), 1);
			assert_eq!(Treasury::spend_period(), 2);
			assert_eq!(Treasury::burn(), Permill(500_000));
			assert_eq!(Treasury::pot(), 0);
			assert_eq!(Treasury::proposal_count(), 0);
		});
	}

	#[test]
	fn minting_works() {
		with_externalities(&mut new_test_ext(), || {
			// Check that accumulate works when we have Some value in Dummy already.
			Treasury::on_minted(100);
			assert_eq!(Treasury::pot(), 100);
		});
	}

	#[test]
	fn spend_proposal_takes_min_deposit() {
		with_externalities(&mut new_test_ext(), || {
			assert_ok!(Treasury::propose_spend(&0, 1, 3));
			assert_eq!(Balances::free_balance(&0), 99);
			assert_eq!(Balances::reserved_balance(&0), 1);
		});
	}

	#[test]
	fn spend_proposal_takes_proportional_deposit() {
		with_externalities(&mut new_test_ext(), || {
			assert_ok!(Treasury::propose_spend(&0, 100, 3));
			assert_eq!(Balances::free_balance(&0), 95);
			assert_eq!(Balances::reserved_balance(&0), 5);
		});
	}

	#[test]
	fn spend_proposal_fails_when_proposer_poor() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Treasury::propose_spend(&2, 100, 3), "Proposer's balance too low");
		});
	}

	#[test]
	fn accepted_spend_proposal_ignored_outside_spend_period() {
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_minted(100);

			assert_ok!(Treasury::propose_spend(&0, 100, 3));
			assert_ok!(Treasury::approve_proposal(0));

			<Treasury as OnFinalise<u64>>::on_finalise(1);
			assert_eq!(Balances::free_balance(&3), 0);
			assert_eq!(Treasury::pot(), 100);
		});
	}

	#[test]
	fn unused_pot_should_diminish() {
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_minted(100);

			<Treasury as OnFinalise<u64>>::on_finalise(2);
			assert_eq!(Treasury::pot(), 50);
		});
	}

	#[test]
	fn rejected_spend_proposal_ignored_on_spend_period() {
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_minted(100);

			assert_ok!(Treasury::propose_spend(&0, 100, 3));
			assert_ok!(Treasury::reject_proposal(0));

			<Treasury as OnFinalise<u64>>::on_finalise(2);
			assert_eq!(Balances::free_balance(&3), 0);
			assert_eq!(Treasury::pot(), 50);
		});
	}

	#[test]
	fn reject_already_rejected_spend_proposal_fails() {
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_minted(100);

			assert_ok!(Treasury::propose_spend(&0, 100, 3));
			assert_ok!(Treasury::reject_proposal(0));
			assert_noop!(Treasury::reject_proposal(0), "No proposal at that index");
		});
	}

	#[test]
	fn reject_non_existant_spend_proposal_fails() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Treasury::reject_proposal(0), "No proposal at that index");
		});
	}

	#[test]
	fn accept_non_existant_spend_proposal_fails() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Treasury::approve_proposal(0), "No proposal at that index");
		});
	}

	#[test]
	fn accept_already_rejected_spend_proposal_fails() {
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_minted(100);

			assert_ok!(Treasury::propose_spend(&0, 100, 3));
			assert_ok!(Treasury::reject_proposal(0));
			assert_noop!(Treasury::approve_proposal(0), "No proposal at that index");
		});
	}

	#[test]
	fn accepted_spend_proposal_enacted_on_spend_period() {
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_minted(100);

			assert_ok!(Treasury::propose_spend(&0, 100, 3));
			assert_ok!(Treasury::approve_proposal(0));

			<Treasury as OnFinalise<u64>>::on_finalise(2);
			assert_eq!(Balances::free_balance(&3), 100);
			assert_eq!(Treasury::pot(), 0);
		});
	}

	#[test]
	fn pot_underflow_should_not_diminish() {
		with_externalities(&mut new_test_ext(), || {
			Treasury::on_minted(100);

			assert_ok!(Treasury::propose_spend(&0, 150, 3));
			assert_ok!(Treasury::approve_proposal(0));

			<Treasury as OnFinalise<u64>>::on_finalise(2);
			assert_eq!(Treasury::pot(), 100);

			Treasury::on_minted(100);
			<Treasury as OnFinalise<u64>>::on_finalise(4);
			assert_eq!(Balances::free_balance(&3), 150);
			assert_eq!(Treasury::pot(), 25);
		});
	}
}
