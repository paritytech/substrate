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

//! Strongly typed API for Substrate runtime.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

extern crate node_primitives as primitives;
extern crate node_runtime as runtime;
extern crate substrate_client as client;
extern crate sr_primitives;
extern crate substrate_primitives;

pub use client::error::{Error, ErrorKind, Result};
use runtime::Address;
use client::backend::Backend;
use client::block_builder::BlockBuilder as ClientBlockBuilder;
use client::{Client, CallExecutor};
use primitives::{
	AccountId, Block, BlockId, BlockNumber, Hash, Index, InherentData, SessionKey, Timestamp, UncheckedExtrinsic
};
use sr_primitives::{transaction_validity::TransactionValidity, traits::{GetHeight, BlockNumberToHash}};
use substrate_primitives::{Blake2Hasher, RlpCodec};

/// Build new blocks.
pub trait BlockBuilder {
	/// Push an extrinsic onto the block. Fails if the extrinsic is invalid.
	fn push_extrinsic(&mut self, extrinsic: UncheckedExtrinsic) -> Result<()>;

	/// Bake the block with provided extrinsics.
	fn bake(self) -> Result<Block>;
}

/// Trait encapsulating the node API.
///
/// All calls should fail when the exact runtime is unknown.
pub trait Api: GetHeight<BlockNumber=BlockNumber> + BlockNumberToHash<BlockNumber=BlockNumber,Hash=Hash> {
	/// The block builder for this API type.
	type BlockBuilder: BlockBuilder;

	/// Get session keys at a given block.
	fn session_keys(&self, at: &BlockId) -> Result<Vec<SessionKey>>;

	/// Get validators at a given block.
	fn validators(&self, at: &BlockId) -> Result<Vec<AccountId>>;

	/// Get the value of the randomness beacon at a given block.
	fn random_seed(&self, at: &BlockId) -> Result<Hash>;

	/// Get the timestamp registered at a block.
	fn timestamp(&self, at: &BlockId) -> Result<Timestamp>;

	// TODO: remove in favour of validate_transaction

	/// Get the nonce (né index) of an account at a block.
	fn index(&self, at: &BlockId, account: AccountId) -> Result<Index>;

	/// Get the account id of an address at a block.
	fn lookup(&self, at: &BlockId, address: Address) -> Result<Option<AccountId>>;

	/// Validate a transaction and determine its dependencies.
	fn validate_transaction(&self, at: &BlockId, transaction: UncheckedExtrinsic) -> Result<TransactionValidity>;

	/// Evaluate a block. Returns true if the block is good, false if it is known to be bad,
	/// and an error if we can't evaluate for some reason.
	fn evaluate_block(&self, at: &BlockId, block: Block) -> Result<bool>;

	/// Build a block on top of the given, with inherent extrinsics pre-pushed.
	fn build_block(&self, at: &BlockId, inherent_data: InherentData) -> Result<Self::BlockBuilder>;

	/// Attempt to produce the (encoded) inherent extrinsics for a block being built upon the given.
	/// This may vary by runtime and will fail if a runtime doesn't follow the same API.
	fn inherent_extrinsics(&self, at: &BlockId, inherent_data: InherentData) -> Result<Vec<UncheckedExtrinsic>>;
}

impl<B, E> BlockBuilder for ClientBlockBuilder<B, E, Block, Blake2Hasher, RlpCodec>
where
	B: Backend<Block, Blake2Hasher, RlpCodec>,
	E: CallExecutor<Block, Blake2Hasher, RlpCodec> + Clone,
{
	fn push_extrinsic(&mut self, extrinsic: UncheckedExtrinsic) -> Result<()> {
		self.push(extrinsic).map_err(Into::into)
	}

	/// Bake the block with provided extrinsics.
	fn bake(self) -> Result<Block> {
		ClientBlockBuilder::bake(self).map_err(Into::into)
	}
}

impl<B, E> Api for Client<B, E, Block>
where
	B: Backend<Block, Blake2Hasher, RlpCodec>,
	E: CallExecutor<Block, Blake2Hasher, RlpCodec> + Clone,
{
	type BlockBuilder = ClientBlockBuilder<B, E, Block, Blake2Hasher, RlpCodec>;

	fn session_keys(&self, at: &BlockId) -> Result<Vec<SessionKey>> {
		Ok(self.authorities_at(at)?)
	}

	fn validators(&self, at: &BlockId) -> Result<Vec<AccountId>> {
		self.call_api_at(at, "validators", &())
	}

	fn random_seed(&self, at: &BlockId) -> Result<Hash> {
		self.call_api_at(at, "random_seed", &())
	}

	fn timestamp(&self, at: &BlockId) -> Result<Timestamp> {
		self.call_api_at(at, "timestamp", &())
	}

	fn evaluate_block(&self, at: &BlockId, block: Block) -> Result<bool> {
		let res: Result<()> = self.call_api_at(at, "execute_block", &block);
		match res {
			Ok(()) => Ok(true),
			Err(err) => match err.kind() {
				&client::error::ErrorKind::Execution(_) => Ok(false),
				_ => Err(err)
			}
		}
	}

	fn index(&self, at: &BlockId, account: AccountId) -> Result<Index> {
		self.call_api_at(at, "account_nonce", &account)
	}

	fn lookup(&self, at: &BlockId, address: Address) -> Result<Option<AccountId>> {
		self.call_api_at(at, "lookup_address", &address)
	}

	fn validate_transaction(&self, at: &BlockId, tx: UncheckedExtrinsic) -> Result<TransactionValidity> {
		self.call_api_at(at, "validate_transaction", &tx)
	}

	fn build_block(&self, at: &BlockId, inherent_data: InherentData) -> Result<Self::BlockBuilder> {
		let runtime_version = self.runtime_version_at(at)?;

		let mut block_builder = self.new_block_at(at)?;
		if runtime_version.has_api(*b"inherent", 1) {
			for inherent in self.inherent_extrinsics(at, inherent_data)? {
				block_builder.push(inherent)?;
			}
		}
		Ok(block_builder)
	}

	fn inherent_extrinsics(&self, at: &BlockId, inherent_data: InherentData) -> Result<Vec<UncheckedExtrinsic>> {
		self.call_api_at(at, "inherent_extrinsics", &inherent_data)
	}
}

