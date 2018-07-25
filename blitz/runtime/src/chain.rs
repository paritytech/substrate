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
use primitives::{NodeId, AccountId, Balance};
use {system, session};

// use substrate_runtime_support::{StorageValue, StorageMap};
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
		// provide candidate receipts for parachains, in ascending order by id.
		fn register_node(aux, id: NodeId, income: AccountId, collateral: AccountId) -> Result = 0;
		fn deregister_node(aux, id: NodeId) -> Result = 1;

		fn transfer(aux, from: AccountId, to: AccountId, amount: Balance) -> Result = 2;
	}
}

decl_storage! {
	trait Store for Module<T: Trait>;

	// Maps account id to its balance
	pub AccountBalance get(account_balance): b"blz:ab" => map [ AccountId => Balance ];

	// Maps account id to its CTH
	pub AccountCTH get(account_cth): b"blz:acth" => map [ AccountId => Balance ];

	// Maps node id to its income account
	pub IncomeAccount get(income_account): b"blz:nia" => map [ NodeId => AccountId ];

	// Maps node id to its collateral account
	pub CollateralAccount get(collateral_account): b"blz:nca" => map [ NodeId => AccountId ];

	// Maps node id to a list of its network addresses
	pub NodeAddresses get(node_addresses): b"blz:na" => map [ NodeId => Vec<Vec<u8>> ];

	// How many rounds should be sealed within one block of the chain
	pub RoundsPerBlock get(rounds_per_block): b"blz:rpb" => u32;

	// How many transactions may be processed by a network per round at max
	pub TransactionsPerRound get(transactions_per_round): b"blz:tpr" => u32;

	// MaxConsensus system variable from the Blitz whitepaper
	pub MaxConsensus get(max_consensus): b"blz:mxc" => u32;
}

impl<T: Trait> Module<T> {
	fn register_node(aux: &<T as Trait>::PublicAux, id: NodeId, income: AccountId, collateral: AccountId) -> Result {
		unimplemented!()
	}

	fn deregister_node(aux: &<T as Trait>::PublicAux, id: NodeId) -> Result {
		unimplemented!()
	}

	fn transfer(aux: &<T as Trait>::PublicAux, from: AccountId, to: AccountId, amount: Balance) -> Result {
		

		unimplemented!()
	}

}
