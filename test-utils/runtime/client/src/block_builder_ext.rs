// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Block Builder extensions for tests.

use sc_client_api::backend;
use sp_api::{ApiExt, ProvideRuntimeApi};

use sc_block_builder::BlockBuilderApi;

/// Extension trait for test block builder.
pub trait BlockBuilderExt {
	/// Add transfer extrinsic to the block.
	fn push_transfer(
		&mut self,
		transfer: substrate_test_runtime::Transfer,
	) -> Result<(), sp_blockchain::Error>;
	/// Add storage change extrinsic to the block.
	fn push_storage_change(
		&mut self,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	) -> Result<(), sp_blockchain::Error>;
}

impl<'a, A, B> BlockBuilderExt
	for sc_block_builder::BlockBuilder<'a, substrate_test_runtime::Block, A, B>
where
	A: ProvideRuntimeApi<substrate_test_runtime::Block> + 'a,
	A::Api: BlockBuilderApi<substrate_test_runtime::Block>
		+ ApiExt<
			substrate_test_runtime::Block,
			StateBackend = backend::StateBackendFor<B, substrate_test_runtime::Block>,
		>,
	B: backend::Backend<substrate_test_runtime::Block>,
{
	fn push_transfer(
		&mut self,
		transfer: substrate_test_runtime::Transfer,
	) -> Result<(), sp_blockchain::Error> {
		self.push(transfer.into_signed_tx())
	}

	fn push_storage_change(
		&mut self,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	) -> Result<(), sp_blockchain::Error> {
		self.push(substrate_test_runtime::Extrinsic::StorageChange(key, value))
	}
}
