// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo. If not, see <http://www.gnu.org/licenses/>.

//! Definition of Substrate module for Blitz.

#![allow(dead_code, unreachable_patterns)]

use rstd::prelude::*;
use codec::Decode;

use runtime_primitives::traits::{Hash, BlakeTwo256, Executable, RefInto, MaybeEmpty};
// use primitives::parachain::{Id, Chain, DutyRoster, CandidateReceipt};
use primitives::{NodeId, AccountId, Balance, Amount, CTH};
use {system, session};

use substrate_runtime_support::{StorageValue, StorageMap};
use substrate_runtime_support::dispatch::Result;

// #[cfg(any(feature = "std", test))]
// use rstd::marker::PhantomData;

// #[cfg(any(feature = "std", test))]
// use {runtime_io, runtime_primitives};

pub trait Trait: system::Trait<Hash = ::primitives::Hash> + session::Trait {
	type PublicAux: RefInto<Self::AccountId> + MaybeEmpty;
}

decl_module! {
	/// Blitz module.
	pub struct Module<T: Trait>;

	/// Call type for Blitz.
	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: <T as Trait>::PublicAux {
		// Register a new node which later may be acted as locker and receive income
		fn register_node(aux, id: NodeId, income: AccountId, collateral: AccountId) -> Result = 0;

		// Deregister the node and free its collateral funds
		fn deregister_node(aux, id: NodeId) -> Result = 1;

		// Transfer funds from one account to another
		fn transfer(aux, from: AccountId, to: AccountId, amount: Amount) -> Result = 2;
	}
}

decl_storage! {
	trait Store for Module<T: Trait>;

	// Maps account id to its balance
	pub AccountBalance get(account_balance): b"blz:ab" => default map [ AccountId => Balance ];

	// Maps account id to its CTH
	pub AccountCTH get(account_cth): b"blz:acth" => map [ AccountId => CTH ];

	// Maps node id to its income account
	pub IncomeAccount get(income_account): b"blz:nia" => map [ NodeId => AccountId ];

	// Maps node id to its collateral (staking) account
	pub NodeToCollateral get(node_to_collateral): b"blz:n2c" => map [ NodeId => AccountId ];

	// Maps collateral account to node id that it is tied to
	pub CollateralToNode get(collateral_to_node): b"blz:c2n" => map [ AccountId => NodeId ];

	// Maps node id to a list of its network addresses
	pub NodeAddresses get(node_addresses): b"blz:na" => map [ NodeId => Vec<Vec<u8>> ];

	// How much does it cost to register a new node
	pub NodeRegistrationFee get(node_registration_fee): b"blz:rpb" => Amount;

	// How many rounds should be sealed within one block of the chain
	pub RoundsPerBlock get(rounds_per_block): b"blz:rpb" => u32;

	// How many transactions may be processed by a network per round at max
	pub TransactionsPerRound get(transactions_per_round): b"blz:tpr" => u32;

	// MaxConsensus system variable from the Blitz whitepaper
	pub MaxConsensus get(max_consensus): b"blz:mxc" => u32;
}

impl<T: Trait> Module<T> {
	fn register_node(_aux: &<T as Trait>::PublicAux, node: NodeId, income: AccountId, collateral: AccountId) -> Result {
		// Performing some consistency checks
		ensure!(!<NodeToCollateral<T>>::exists(node), "node already exists");
		ensure!(!<IncomeAccount<T>>::exists(node), "income account already set");
		ensure!(!<CollateralToNode<T>>::exists(collateral), "collateral is already in use");

		ensure!(<AccountCTH<T>>::exists(collateral), "collateral account does not exist");
		ensure!(<NodeRegistrationFee<T>>::exists(), "registration fee is not set");
		let collateral_balance = <AccountBalance<T>>::get(collateral);
		let registration_fee = <NodeRegistrationFee<T>>::get().unwrap();

		// Taking the registration fee
		ensure!(collateral_balance > registration_fee, "not enough collateral funds");
		<AccountBalance<T>>::insert(collateral, collateral_balance - registration_fee);

		// Registering node and its accounts
		<CollateralToNode<T>>::insert(collateral, node);
		<NodeToCollateral<T>>::insert(node, collateral);
		<IncomeAccount<T>>::insert(node, income);

		// Welcome to the club
		Ok(())
	}

	fn deregister_node(_aux: &<T as Trait>::PublicAux, id: NodeId) -> Result {
		unimplemented!()
	}

	fn transfer(_aux: &<T as Trait>::PublicAux, from: AccountId, to: AccountId, amount: Amount) -> Result {
		// Affected accounts should not be collateral
		ensure!(!<CollateralToNode<T>>::exists(from), "source account is locked as collateral");
		ensure!(!<CollateralToNode<T>>::exists(to), "destination account is locked as collateral");

		let from_balance = <AccountBalance<T>>::get(from);
		let to_balance = <AccountBalance<T>>::get(to);

		ensure!(from_balance > amount, "not enough funds");
		<AccountBalance<T>>::insert(from, from_balance - amount);
		<AccountBalance<T>>::insert(to, to_balance.checked_add(amount).expect("balance overflow"));

		Ok(())
	}

}
