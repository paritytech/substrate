// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! State objects specific to the Blitz protocol

#![allow(dead_code)]

extern crate blitz_primitives;
extern crate blitz_network;

use blitz_primitives::{PublicKey, Hash, Balance, RoundId};
use blitz_network::transaction::SignedTransaction;
use std::collections::{HashMap, HashSet};

pub struct Account {
	public_key: PublicKey,
	cth: Hash,
	balance: Balance,

	first_as_node: Option<RoundId>,
	last_as_node: Option<RoundId>,

	num_operations: usize,
	last_modified: RoundId,
	last_transaction: Hash,
}

#[derive(Default)]
pub struct AccountStore {
	accounts: HashMap<Hash, Account>,
	public_keys: HashSet<PublicKey>,
}

impl AccountStore {
	pub fn get_by_key(&self, key: PublicKey) -> Option<&Account> {
		unimplemented!()
	}

	pub fn get_by_cth(&self, cth: Hash) -> Option<&Account> {
		unimplemented!()
	}
}

#[derive(Default)]
pub struct GlobalState {
	genesis_round_id: RoundId, // TODO [dk] should probably be in the config
	account_store: AccountStore,
}

struct Node {

}

struct NodeStore {

}

impl NodeStore {
	pub fn get_locker(id: PublicKey, global_state_hash: Hash) -> Node {
		unimplemented!()
	}
}

struct TransactionStore {
}

pub struct BlitzRound {
	transactions: Vec<SignedTransaction>,
}

pub struct BlitzBlock {
	rounds: Vec<Round>,
}
