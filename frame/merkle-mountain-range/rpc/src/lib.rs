// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

#![warn(missing_docs)]
#![warn(unused_crate_dependencies)]

//! Node-specific RPC methods for interaction with Merkle Mountain Range pallet.

use std::{marker::PhantomData, sync::Arc};

use codec::{Codec, Encode};
use jsonrpsee::{
	core::{async_trait, RpcResult},
	proc_macros::rpc,
	types::error::{CallError, ErrorObject},
};
use serde::{Deserialize, Serialize};

use sp_api::{NumberFor, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_core::Bytes;
use sp_mmr_primitives::{BatchProof, Error as MmrError, Proof};
use sp_runtime::{generic::BlockId, traits::Block as BlockT};

pub use sp_mmr_primitives::MmrApi as MmrRuntimeApi;

const RUNTIME_ERROR: i32 = 8000;
const MMR_ERROR: i32 = 8010;
const LEAF_NOT_FOUND_ERROR: i32 = MMR_ERROR + 1;
const GENERATE_PROOF_ERROR: i32 = MMR_ERROR + 2;

/// Retrieved MMR leaf and its proof.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct LeafProof<BlockHash> {
	/// Block hash the proof was generated for.
	pub block_hash: BlockHash,
	/// SCALE-encoded leaf data.
	pub leaf: Bytes,
	/// SCALE-encoded proof data. See [sp_mmr_primitives::Proof].
	pub proof: Bytes,
}

impl<BlockHash> LeafProof<BlockHash> {
	/// Create new `LeafProof` from given concrete `leaf` and `proof`.
	pub fn new<Leaf, MmrHash>(block_hash: BlockHash, leaf: Leaf, proof: Proof<MmrHash>) -> Self
	where
		Leaf: Encode,
		MmrHash: Encode,
	{
		Self { block_hash, leaf: Bytes(leaf.encode()), proof: Bytes(proof.encode()) }
	}
}

/// Retrieved MMR leaves and their proof.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct LeafBatchProof<BlockHash> {
	/// Block hash the proof was generated for.
	pub block_hash: BlockHash,
	/// SCALE-encoded vector of `LeafData`.
	pub leaves: Bytes,
	/// SCALE-encoded proof data. See [sp_mmr_primitives::BatchProof].
	pub proof: Bytes,
}

impl<BlockHash> LeafBatchProof<BlockHash> {
	/// Create new `LeafBatchProof` from a given vector of `Leaf` and a
	/// [sp_mmr_primitives::BatchProof].
	pub fn new<Leaf, MmrHash>(
		block_hash: BlockHash,
		leaves: Vec<Leaf>,
		proof: BatchProof<MmrHash>,
	) -> Self
	where
		Leaf: Encode,
		MmrHash: Encode,
	{
		Self { block_hash, leaves: Bytes(leaves.encode()), proof: Bytes(proof.encode()) }
	}
}

/// MMR RPC methods.
#[rpc(client, server)]
pub trait MmrApi<BlockHash, BlockNumber> {
	/// Generate MMR proof for given block number.
	///
	/// This method calls into a runtime with MMR pallet included and attempts to generate
	/// MMR proof for a block with a specified `block_number`.
	/// Optionally, a block hash at which the runtime should be queried can be specified.
	///
	/// Returns the (full) leaf itself and a proof for this leaf (compact encoding, i.e. hash of
	/// the leaf). Both parameters are SCALE-encoded.
	#[method(name = "mmr_generateProof")]
	fn generate_proof(
		&self,
		block_number: BlockNumber,
		at: Option<BlockHash>,
	) -> RpcResult<LeafProof<BlockHash>>;

	/// Generate MMR proof for the given block numbers.
	///
	/// This method calls into a runtime with MMR pallet included and attempts to generate
	/// MMR proof for a set of blocks with the specific `block_numbers`.
	/// Optionally, a block hash at which the runtime should be queried can be specified.
	///
	/// Returns the leaves and a proof for these leaves (compact encoding, i.e. hash of
	/// the leaves). Both parameters are SCALE-encoded.
	/// The order of entries in the `leaves` field of the returned struct
	/// is the same as the order of the entries in `block_numbers` supplied
	#[method(name = "mmr_generateBatchProof")]
	fn generate_batch_proof(
		&self,
		block_numbers: Vec<BlockNumber>,
		at: Option<BlockHash>,
	) -> RpcResult<LeafBatchProof<BlockHash>>;

	/// Generate a MMR proof for the given `block_numbers` given the `best_known_block_number`.
	///
	/// This method calls into a runtime with MMR pallet included and attempts to generate
	/// a MMR proof for the set of blocks that have the given `block_numbers` with MMR given the
	/// `best_known_block_number`. `best_known_block_number` must be larger than all the
	/// `block_numbers` for the function to succeed.
	///
	/// Optionally, a block hash at which the runtime should be queried can be specified.
	/// Note that specifying the block hash isn't super-useful here, unless you're generating
	/// proof using non-finalized blocks where there are several competing forks. That's because
	/// MMR state will be fixed to the state with `best_known_block_number`, which already points to
	/// some historical block.
	///
	/// Returns the leaves and a proof for these leaves (compact encoding, i.e. hash of
	/// the leaves). Both parameters are SCALE-encoded.
	/// The order of entries in the `leaves` field of the returned struct
	/// is the same as the order of the entries in `block_numbers` supplied
	#[method(name = "mmr_generateHistoricalBatchProof")]
	fn generate_historical_batch_proof(
		&self,
		block_numbers: Vec<BlockNumber>,
		best_known_block_number: BlockNumber,
		at: Option<BlockHash>,
	) -> RpcResult<LeafBatchProof<BlockHash>>;
}

/// MMR RPC methods.
pub struct Mmr<Client, Block> {
	client: Arc<Client>,
	_marker: PhantomData<Block>,
}

impl<C, B> Mmr<C, B> {
	/// Create new `Mmr` with the given reference to the client.
	pub fn new(client: Arc<C>) -> Self {
		Self { client, _marker: Default::default() }
	}
}

#[async_trait]
impl<Client, Block, MmrHash> MmrApiServer<<Block as BlockT>::Hash, NumberFor<Block>>
	for Mmr<Client, (Block, MmrHash)>
where
	Block: BlockT,
	Client: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	Client::Api: MmrRuntimeApi<Block, MmrHash, NumberFor<Block>>,
	MmrHash: Codec + Send + Sync + 'static,
{
	fn generate_proof(
		&self,
		block_number: NumberFor<Block>,
		at: Option<<Block as BlockT>::Hash>,
	) -> RpcResult<LeafProof<Block::Hash>> {
		let api = self.client.runtime_api();
		let block_hash = at.unwrap_or_else(|| self.client.info().best_hash);

		let (leaf, proof) = api
			.generate_proof_with_context(
				&BlockId::hash(block_hash),
				sp_core::ExecutionContext::OffchainCall(None),
				block_number,
			)
			.map_err(runtime_error_into_rpc_error)?
			.map_err(mmr_error_into_rpc_error)?;

		Ok(LeafProof::new(block_hash, leaf, proof))
	}

	fn generate_batch_proof(
		&self,
		block_numbers: Vec<NumberFor<Block>>,
		at: Option<<Block as BlockT>::Hash>,
	) -> RpcResult<LeafBatchProof<<Block as BlockT>::Hash>> {
		let api = self.client.runtime_api();
		let block_hash = at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash);

		let (leaves, proof) = api
			.generate_batch_proof_with_context(
				&BlockId::hash(block_hash),
				sp_core::ExecutionContext::OffchainCall(None),
				block_numbers,
			)
			.map_err(runtime_error_into_rpc_error)?
			.map_err(mmr_error_into_rpc_error)?;

		Ok(LeafBatchProof::new(block_hash, leaves, proof))
	}

	fn generate_historical_batch_proof(
		&self,
		block_numbers: Vec<NumberFor<Block>>,
		best_known_block_number: NumberFor<Block>,
		at: Option<<Block as BlockT>::Hash>,
	) -> RpcResult<LeafBatchProof<<Block as BlockT>::Hash>> {
		let api = self.client.runtime_api();
		let block_hash = at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash);

		let (leaves, proof) = api
			.generate_historical_batch_proof_with_context(
				&BlockId::hash(block_hash),
				sp_core::ExecutionContext::OffchainCall(None),
				block_numbers,
				best_known_block_number,
			)
			.map_err(runtime_error_into_rpc_error)?
			.map_err(mmr_error_into_rpc_error)?;

		Ok(LeafBatchProof::new(block_hash, leaves, proof))
	}
}

/// Converts a mmr-specific error into a [`CallError`].
fn mmr_error_into_rpc_error(err: MmrError) -> CallError {
	let data = format!("{:?}", err);
	match err {
		MmrError::LeafNotFound => CallError::Custom(ErrorObject::owned(
			LEAF_NOT_FOUND_ERROR,
			"Leaf was not found",
			Some(data),
		)),
		MmrError::GenerateProof => CallError::Custom(ErrorObject::owned(
			GENERATE_PROOF_ERROR,
			"Error while generating the proof",
			Some(data),
		)),
		_ => CallError::Custom(ErrorObject::owned(MMR_ERROR, "Unexpected MMR error", Some(data))),
	}
}

/// Converts a runtime trap into a [`CallError`].
fn runtime_error_into_rpc_error(err: impl std::fmt::Debug) -> CallError {
	CallError::Custom(ErrorObject::owned(
		RUNTIME_ERROR,
		"Runtime trapped",
		Some(format!("{:?}", err)),
	))
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::H256;

	#[test]
	fn should_serialize_leaf_proof() {
		// given
		let leaf = vec![1_u8, 2, 3, 4];
		let proof = Proof {
			leaf_index: 1,
			leaf_count: 9,
			items: vec![H256::repeat_byte(1), H256::repeat_byte(2)],
		};

		let leaf_proof = LeafProof::new(H256::repeat_byte(0), leaf, proof);

		// when
		let actual = serde_json::to_string(&leaf_proof).unwrap();

		// then
		assert_eq!(
			actual,
			r#"{"blockHash":"0x0000000000000000000000000000000000000000000000000000000000000000","leaf":"0x1001020304","proof":"0x010000000000000009000000000000000801010101010101010101010101010101010101010101010101010101010101010202020202020202020202020202020202020202020202020202020202020202"}"#
		);
	}

	#[test]
	fn should_serialize_leaf_batch_proof() {
		// given
		let leaf = vec![1_u8, 2, 3, 4];
		let proof = BatchProof {
			leaf_indices: vec![1],
			leaf_count: 9,
			items: vec![H256::repeat_byte(1), H256::repeat_byte(2)],
		};

		let leaf_proof = LeafBatchProof::new(H256::repeat_byte(0), vec![leaf], proof);

		// when
		let actual = serde_json::to_string(&leaf_proof).unwrap();

		// then
		assert_eq!(
			actual,
			r#"{"blockHash":"0x0000000000000000000000000000000000000000000000000000000000000000","leaves":"0x041001020304","proof":"0x04010000000000000009000000000000000801010101010101010101010101010101010101010101010101010101010101010202020202020202020202020202020202020202020202020202020202020202"}"#
		);
	}

	#[test]
	fn should_deserialize_leaf_proof() {
		// given
		let expected = LeafProof {
			block_hash: H256::repeat_byte(0),
			leaf: Bytes(vec![1_u8, 2, 3, 4].encode()),
			proof: Bytes(
				Proof {
					leaf_index: 1,
					leaf_count: 9,
					items: vec![H256::repeat_byte(1), H256::repeat_byte(2)],
				}
				.encode(),
			),
		};

		// when
		let actual: LeafProof<H256> = serde_json::from_str(r#"{
			"blockHash":"0x0000000000000000000000000000000000000000000000000000000000000000",
			"leaf":"0x1001020304",
			"proof":"0x010000000000000009000000000000000801010101010101010101010101010101010101010101010101010101010101010202020202020202020202020202020202020202020202020202020202020202"
		}"#).unwrap();

		// then
		assert_eq!(actual, expected);
	}

	#[test]
	fn should_deserialize_leaf_batch_proof() {
		// given
		let expected = LeafBatchProof {
			block_hash: H256::repeat_byte(0),
			leaves: Bytes(vec![vec![1_u8, 2, 3, 4]].encode()),
			proof: Bytes(
				BatchProof {
					leaf_indices: vec![1],
					leaf_count: 9,
					items: vec![H256::repeat_byte(1), H256::repeat_byte(2)],
				}
				.encode(),
			),
		};

		// when
		let actual: LeafBatchProof<H256> = serde_json::from_str(r#"{
			"blockHash":"0x0000000000000000000000000000000000000000000000000000000000000000",
			"leaves":"0x041001020304",
			"proof":"0x04010000000000000009000000000000000801010101010101010101010101010101010101010101010101010101010101010202020202020202020202020202020202020202020202020202020202020202"
		}"#).unwrap();

		// then
		assert_eq!(actual, expected);
	}
}
