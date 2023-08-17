// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use substrate_test_runtime::*;

/// Extension trait for test block builder.
pub trait BlockBuilderExt {
	/// Add transfer extrinsic to the block.
	fn push_transfer(
		&mut self,
		transfer: substrate_test_runtime::Transfer,
	) -> Result<(), sp_blockchain::Error>;

	/// Add unsigned storage change extrinsic to the block.
	fn push_storage_change(
		&mut self,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	) -> Result<(), sp_blockchain::Error>;

	/// Adds an extrinsic which pushes DigestItem to header's log
	fn push_deposit_log_digest_item(
		&mut self,
		log: sp_runtime::generic::DigestItem,
	) -> Result<(), sp_blockchain::Error>;
}

impl<'a, A, B> BlockBuilderExt
	for sc_block_builder::BlockBuilder<'a, substrate_test_runtime::Block, A, B>
where
	A: ProvideRuntimeApi<substrate_test_runtime::Block> + 'a,
	A::Api: BlockBuilderApi<substrate_test_runtime::Block> + ApiExt<substrate_test_runtime::Block>,
	B: backend::Backend<substrate_test_runtime::Block>,
{
	fn push_transfer(
		&mut self,
		transfer: substrate_test_runtime::Transfer,
	) -> Result<(), sp_blockchain::Error> {
		self.push(transfer.into_unchecked_extrinsic())
	}

	fn push_storage_change(
		&mut self,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	) -> Result<(), sp_blockchain::Error> {
		self.push(ExtrinsicBuilder::new_storage_change(key, value).build())
	}

	fn push_deposit_log_digest_item(
		&mut self,
		log: sp_runtime::generic::DigestItem,
	) -> Result<(), sp_blockchain::Error> {
		self.push(ExtrinsicBuilder::new_deposit_log_digest_item(log).build())
	}
}
