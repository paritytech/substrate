// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

//! Block Builder extensions for tests.

use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_core::ChangesTrieConfiguration;
use sc_client_api::backend;
use sp_runtime::traits::HashFor;

use sc_block_builder::BlockBuilderApi;

/// Extension trait for test block builder.
pub trait BlockBuilderExt {
	/// Add transfer extrinsic to the block.
	fn push_transfer(&mut self, transfer: substrate_test_runtime::Transfer) -> Result<(), sp_blockchain::Error>;
	/// Add storage change extrinsic to the block.
	fn push_storage_change(
		&mut self,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	) -> Result<(), sp_blockchain::Error>;
	/// Add changes trie configuration update extrinsic to the block.
	fn push_changes_trie_configuration_update(
		&mut self,
		new_config: Option<ChangesTrieConfiguration>,
	) -> Result<(), sp_blockchain::Error>;
}

impl<'a, A, B> BlockBuilderExt for sc_block_builder::BlockBuilder<'a, substrate_test_runtime::Block, A, B> where
	A: ProvideRuntimeApi<substrate_test_runtime::Block> + 'a,
	A::Api: BlockBuilderApi<substrate_test_runtime::Block, Error = sp_blockchain::Error> +
		ApiExt<
			substrate_test_runtime::Block,
			StateBackend = backend::StateBackendFor<B, substrate_test_runtime::Block>
		>,
	B: backend::Backend<substrate_test_runtime::Block>,
	// Rust bug: https://github.com/rust-lang/rust/issues/24159
	backend::StateBackendFor<B, substrate_test_runtime::Block>:
		sp_api::StateBackend<HashFor<substrate_test_runtime::Block>>,
{
	fn push_transfer(&mut self, transfer: substrate_test_runtime::Transfer) -> Result<(), sp_blockchain::Error> {
		self.push(transfer.into_signed_tx())
	}

	fn push_storage_change(
		&mut self,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	) -> Result<(), sp_blockchain::Error> {
		self.push(substrate_test_runtime::Extrinsic::StorageChange(key, value))
	}

	fn push_changes_trie_configuration_update(
		&mut self,
		new_config: Option<ChangesTrieConfiguration>,
	) -> Result<(), sp_blockchain::Error> {
		self.push(substrate_test_runtime::Extrinsic::ChangesTrieConfigUpdate(new_config))
	}
}
