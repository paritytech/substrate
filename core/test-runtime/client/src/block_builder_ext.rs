// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

use runtime;
use runtime_primitives::traits::ProvideRuntimeApi;
use generic_test_client::client;
use generic_test_client::client::block_builder::api::BlockBuilder;

/// Extension trait for test block builder.
pub trait BlockBuilderExt {
	/// Add transfer extrinsic to the block.
	fn push_transfer(&mut self, transfer: runtime::Transfer) -> Result<(), client::error::Error>;
	/// Add storage change extrinsic to the block.
	fn push_storage_change(&mut self, key: Vec<u8>, value: Option<Vec<u8>>) -> Result<(), client::error::Error>;
}

impl<'a, A> BlockBuilderExt for client::block_builder::BlockBuilder<'a, runtime::Block, A> where
	A: ProvideRuntimeApi + client::blockchain::HeaderBackend<runtime::Block> + 'a,
	A::Api: BlockBuilder<runtime::Block>
{
	fn push_transfer(&mut self, transfer: runtime::Transfer) -> Result<(), client::error::Error> {
		self.push(transfer.into_signed_tx())
	}

	fn push_storage_change(&mut self, key: Vec<u8>, value: Option<Vec<u8>>) -> Result<(), client::error::Error> {
		self.push(runtime::Extrinsic::StorageChange(key, value))
	}
}
