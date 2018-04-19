// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Client extension for tests.

use codec::Slicable;
use client::{self, Client};
use keyring::Keyring;
use runtime_support::Hashable;
use runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
use primitives::block;
use bft;
use {Backend, Executor, NativeExecutor};

/// Extension trait for a test client.
pub trait TestClient {
	/// Crates new client instance for tests.
	fn new_for_tests() -> Self;

	/// Justify and import block to the chain.
	fn justify_and_import(&self, origin: client::BlockOrigin, block: block::Block) -> client::error::Result<()>;

	/// Returns hash of the genesis block.
	fn genesis_hash(&self) -> block::HeaderHash;
}

impl TestClient for Client<Backend, Executor> {
	fn new_for_tests() -> Self {
		client::new_in_mem(NativeExecutor::new(), prepare_genesis).unwrap()
	}

	fn justify_and_import(&self, origin: client::BlockOrigin, block: block::Block) -> client::error::Result<()> {
		let justification = fake_justify(&block.header);
		let justified = self.check_justification(block.header, justification)?;
		self.import_block(origin, justified, Some(block.transactions))?;

		Ok(())
	}

	fn genesis_hash(&self) -> block::HeaderHash {
		self.block_hash(0).unwrap().unwrap()
	}
}

/// Prepare fake justification for the header.
///
/// since we are in the client module we can create falsely justified
/// headers.
/// TODO: remove this in favor of custom verification pipelines for the
/// client
fn fake_justify(header: &block::Header) -> bft::UncheckedJustification {
	let hash = header.blake2_256().into();
	let authorities = vec![
		Keyring::Alice.into(),
		Keyring::Bob.into(),
		Keyring::Charlie.into(),
	];

	bft::UncheckedJustification {
		digest: hash,
		signatures: authorities.iter().map(|key| {
			let msg = bft::sign_message(
				bft::generic::Vote::Commit(1, hash).into(),
				key,
				header.parent_hash
			);

			match msg {
				bft::generic::LocalizedMessage::Vote(vote) => vote.signature,
				_ => panic!("signing vote leads to signed vote"),
			}
		}).collect(),
		round_number: 1,
	}
}

fn genesis_config() -> GenesisConfig {
	GenesisConfig::new_simple(vec![
		Keyring::Alice.to_raw_public(),
		Keyring::Bob.to_raw_public(),
		Keyring::Charlie.to_raw_public()
	], 1000)
}

fn prepare_genesis() -> (block::Header, Vec<(Vec<u8>, Vec<u8>)>) {
	let mut storage = genesis_config().genesis_map();
	let block = client::genesis::construct_genesis_block(&storage);
	storage.extend(additional_storage_with_genesis(&block));

	(
		block::Header::decode(&mut block.header.encode().as_ref())
			.expect("to_vec() always gives a valid serialisation; qed"),
		storage.into_iter().collect()
	)
}
