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

use client::{self, Client};
use keyring::Keyring;
use runtime_primitives::StorageMap;
use runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
use runtime;
use bft;
use {Backend, Executor, NativeExecutor};

/// Extension trait for a test client.
pub trait TestClient {
	/// Crates new client instance for tests.
	fn new_for_tests() -> Self;

	/// Justify and import block to the chain.
	fn justify_and_import(&self, origin: client::BlockOrigin, block: runtime::Block) -> client::error::Result<()>;

	/// Returns hash of the genesis block.
	fn genesis_hash(&self) -> runtime::Hash;
}

impl TestClient for Client<Backend, Executor, runtime::Block> {
	fn new_for_tests() -> Self {
		client::new_in_mem(NativeExecutor::new(), genesis_storage()).unwrap()
	}

	fn justify_and_import(&self, origin: client::BlockOrigin, block: runtime::Block) -> client::error::Result<()> {
		let justification = fake_justify(&block.header);
		let justified = self.check_justification(block.header, justification)?;
		self.import_block(origin, justified, Some(block.extrinsics))?;

		Ok(())
	}

	fn genesis_hash(&self) -> runtime::Hash {
		self.block_hash(0).unwrap().unwrap()
	}
}

/// Prepare fake justification for the header.
///
/// since we are in the client module we can create falsely justified
/// headers.
/// TODO: remove this in favor of custom verification pipelines for the
/// client
fn fake_justify(header: &runtime::Header) -> bft::UncheckedJustification<runtime::Hash> {
	let hash = header.hash();
	let authorities = vec![
		Keyring::Alice.into(),
		Keyring::Bob.into(),
		Keyring::Charlie.into(),
	];

	bft::UncheckedJustification::new(
		hash,
		authorities.iter().map(|key| {
			let msg = bft::sign_message::<runtime::Block>(
				::rhododendron::Vote::Commit(1, hash).into(),
				key,
				header.parent_hash
			);

			match msg {
				::rhododendron::LocalizedMessage::Vote(vote) => vote.signature,
				_ => panic!("signing vote leads to signed vote"),
			}
		}).collect(),
		1,
	)
}

fn genesis_config() -> GenesisConfig {
	GenesisConfig::new_simple(vec![
		Keyring::Alice.to_raw_public().into(),
		Keyring::Bob.to_raw_public().into(),
		Keyring::Charlie.to_raw_public().into(),
	], 1000)
}

fn genesis_storage() -> StorageMap {
		let mut storage = genesis_config().genesis_map();
		let block: runtime::Block = client::genesis::construct_genesis_block(&storage);
		storage.extend(additional_storage_with_genesis(&block));
		storage
}
