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

//! Tool for creating the genesis block.

use std::collections::HashMap;
use native_runtime::primitives::{Block, Header};
use triehash::trie_root;

/// Create a genesis block, given the initial storage.
pub fn construct_genesis_block(storage: &HashMap<Vec<u8>, Vec<u8>>) -> Block {
	let state_root = trie_root(storage.clone().into_iter()).0;
	let header = Header {
		parent_hash: Default::default(),
		number: 0,
		state_root,
		transaction_root: trie_root(vec![].into_iter()).0,
		digest: Default::default(),
	};
	Block {
		header,
		transactions: vec![],
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use native_runtime::codec::{Slicable, Joiner};
	use native_runtime::support::{one, two, Hashable};
	use native_runtime::runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
	use native_runtime::primitives::{AccountID, Hash, BlockNumber, Transaction,
			UncheckedTransaction, Digest, Function};
	use state_machine::execute;
	use state_machine::OverlayedChanges;
	use state_machine::backend::InMemory;
	use polkadot_executor::executor;
	use primitives::contract::CallData;
	use primitives::ed25519::Pair;

	fn secret_for(who: &AccountID) -> Option<Pair> {
		match who {
			x if *x == one() => Some(Pair::from_seed(b"12345678901234567890123456789012")),
			x if *x == two() => Some("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60".into()),
			_ => None,
		}
	}

	fn construct_block(number: BlockNumber, parent_hash: Hash, state_root: Hash, txs: Vec<Transaction>) -> (Vec<u8>, Hash) {
		use triehash::ordered_trie_root;

		let transactions = txs.into_iter().map(|transaction| {
			let signature = secret_for(&transaction.signed).unwrap()
				.sign(&transaction.to_vec())
				.inner();
			UncheckedTransaction { transaction, signature }
		}).collect::<Vec<_>>();

		let transaction_root = ordered_trie_root(transactions.iter().map(Slicable::to_vec)).0;

		let header = Header {
			parent_hash,
			number,
			state_root,
			transaction_root,
			digest: Digest { logs: vec![], },
		};
		let hash = header.blake2_256();

		(Block { header, transactions }.to_vec(), hash)
	}

	fn block1(genesis_hash: Hash) -> (Vec<u8>, Hash) {
		construct_block(
			1,
			genesis_hash,
			hex!("25e5b37074063ab75c889326246640729b40d0c86932edc527bc80db0e04fe5c"),
			vec![Transaction {
				signed: one(),
				nonce: 0,
				function: Function::StakingTransfer,
				input_data: vec![].join(&two()).join(&69u64),
			}]
		)
	}

	#[test]
	fn construct_genesis_should_work() {
		let mut storage = GenesisConfig::new_simple(
			vec![one(), two()], 1000
		).genesis_map();
		let block = construct_genesis_block(&storage);
		let genesis_hash = block.header.blake2_256();
		storage.extend(additional_storage_with_genesis(&block).into_iter());

		let mut overlay = OverlayedChanges::default();
		let backend = InMemory::from(storage);
		let (b1data, _b1hash) = block1(genesis_hash);

		let _ = execute(
			&backend,
			&mut overlay,
			&executor(),
			"execute_block",
			&CallData(b1data)
		).unwrap();
	}
}
