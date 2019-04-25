// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Block Builder extensions for tests.

use client;
use super::AccountKeyring;
use runtime;
use runtime_primitives::traits::ProvideRuntimeApi;
use client::block_builder::api::BlockBuilder;

/// Extension trait for test block builder.
pub trait BlockBuilderExt {
	/// Add transfer extrinsic to the block.
	fn push_transfer(&mut self, transfer: runtime::Transfer) -> Result<(), client::error::Error>;
}

impl<'a, A> BlockBuilderExt for client::block_builder::BlockBuilder<'a, runtime::Block, A> where
	A: ProvideRuntimeApi + client::blockchain::HeaderBackend<runtime::Block> + 'a,
	A::Api: BlockBuilder<runtime::Block>
{
	fn push_transfer(&mut self, transfer: runtime::Transfer) -> Result<(), client::error::Error> {
		self.push(sign_tx(transfer))
	}
}

fn sign_tx(transfer: runtime::Transfer) -> runtime::Extrinsic {
	let signature = AccountKeyring::from_public(&transfer.from)
		.unwrap()
		.sign(&parity_codec::Encode::encode(&transfer));
	runtime::Extrinsic::Transfer(transfer, signature)
}
