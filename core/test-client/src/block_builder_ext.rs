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

//! Block Builder extensions for tests.

use codec;
use client;
use keyring;
use runtime;
use runtime_primitives::traits::ProvideRuntimeApi;
use client::runtime_api::BlockBuilder;

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
	let signature = keyring::Keyring::from_raw_public(transfer.from.to_fixed_bytes()).unwrap().sign(&codec::Encode::encode(&transfer)).into();
	runtime::Extrinsic { transfer, signature }
}
