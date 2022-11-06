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

use codec::{Codec, Encode, Decode};
use jsonrpsee::{
	core::{async_trait, RpcResult},
	proc_macros::rpc,
	types::error::{CallError, ErrorObject},
};
use serde::{Deserialize, Serialize};

use sp_api::{NumberFor, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_core::Bytes;
use sp_mmr_primitives::{Error as MmrError, Proof};
use sp_runtime::{generic::BlockId, traits::Block as BlockT};

pub use sp_mmr_primitives::MmrApi as MmrRuntimeApi;

const RUNTIME_ERROR: i32 = 8000;
const MMR_ERROR: i32 = 8010;
const LEAF_NOT_FOUND_ERROR: i32 = MMR_ERROR + 1;
const GENERATE_PROOF_ERROR: i32 = MMR_ERROR + 2;
const VERIFY_PROOF_ERROR: i32 = MMR_ERROR + 3;
const BLOCK_NUM_TO_LEAF_INDEX_ERROR: i32 = MMR_ERROR + 4;
const INVALID_BEST_KNOWN_BLOCK_ERROR: i32 = MMR_ERROR + 5;

/// Retrieved MMR leaves and their proof.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct LeavesProof<BlockHash> {
	/// Block hash the proof was generated for.
	pub block_hash: BlockHash,
	/// SCALE-encoded vector of `LeafData`.
	pub leaves: Bytes,
	/// SCALE-encoded proof data. See [sp_mmr_primitives::Proof].
	pub proof: Bytes,
}

impl<BlockHash> LeavesProof<BlockHash> {
	/// Create new `LeavesProof` from a given vector of `Leaf` and a
	/// [sp_mmr_primitives::Proof].
	pub fn new<Leaf, MmrHash>(
		block_hash: BlockHash,
		leaves: Vec<Leaf>,
		proof: Proof<MmrHash>,
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
	/// Generate a MMR proof for the given `block_numbers`.
	///
	/// This method calls into a runtime with MMR pallet included and attempts to generate
	/// a MMR proof for the set of blocks that have the given `block_numbers` with MMR given the
	/// `best_known_block_number`. `best_known_block_number` must be larger than all the
	/// `block_numbers` for the function to succeed.
	///
	/// Optionally via `at`, a block hash at which the runtime should be queried can be specified.
	/// Optionally via `best_known_block_number`, the proof can be generated using the MMR's state
	/// at a specific best block. Note that if `best_known_block_number` is provided, then also
	/// specifying the block hash via `at` isn't super-useful here, unless you're generating proof
	/// using non-finalized blocks where there are several competing forks. That's because MMR state
	/// will be fixed to the state with `best_known_block_number`, which already points to
	/// some historical block.
	///
	/// Returns the (full) leaves and a proof for these leaves (compact encoding, i.e. hash of
	/// the leaves). Both parameters are SCALE-encoded.
	/// The order of entries in the `leaves` field of the returned struct
	/// is the same as the order of the entries in `block_numbers` supplied
	#[method(name = "mmr_generateProof")]
	fn generate_proof(
		&self,
		block_numbers: Vec<BlockNumber>,
		best_known_block_number: Option<BlockNumber>,
		at: Option<BlockHash>,
	) -> RpcResult<LeavesProof<BlockHash>>;

	/// Verify a MMR proof for the given `leaves`
	/// TODO: add docs
	#[method(name = "mmr_verifyProof")]
	fn verify_proof(
		&self,
		proof: LeavesProof<BlockHash>,
	) -> RpcResult<bool>;
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
		block_numbers: Vec<NumberFor<Block>>,
		best_known_block_number: Option<NumberFor<Block>>,
		at: Option<<Block as BlockT>::Hash>,
	) -> RpcResult<LeavesProof<<Block as BlockT>::Hash>> {
		let api = self.client.runtime_api();
		let block_hash = at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash);

		let (leaves, proof) = api
			.generate_proof_with_context(
				&BlockId::hash(block_hash),
				sp_core::ExecutionContext::OffchainCall(None),
				block_numbers,
				best_known_block_number,
			)
			.map_err(runtime_error_into_rpc_error)?
			.map_err(mmr_error_into_rpc_error)?;

		Ok(LeavesProof::new(block_hash, leaves, proof))
	}

	fn verify_proof(
		&self,
		proof: LeavesProof<<Block as BlockT>::Hash>,
	) -> RpcResult<bool> {
		let api = self.client.runtime_api();

		let leaves = Decode::decode(&mut &proof.leaves.0[..])
			.map_err(runtime_error_into_rpc_error)?;

		let decoded_proof = Decode::decode(&mut &proof.proof.0[..])
			.map_err(runtime_error_into_rpc_error)?;

		api.verify_proof_with_context(
			&BlockId::hash(proof.block_hash),
			sp_core::ExecutionContext::OffchainCall(None),
			leaves,
			decoded_proof,
		).map_err(runtime_error_into_rpc_error)?
		 .map_err(mmr_error_into_rpc_error)?;

		Ok(true)
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
		MmrError::Verify => CallError::Custom(ErrorObject::owned(
			VERIFY_PROOF_ERROR,
			"Error while verifying the proof",
			Some(data),
		)),
		MmrError::BlockNumToLeafIndex => CallError::Custom(ErrorObject::owned(
			BLOCK_NUM_TO_LEAF_INDEX_ERROR,
			"Error while converting block number to leaf index",
			Some(data),
		)),
		MmrError::InvalidBestKnownBlock => CallError::Custom(ErrorObject::owned(
			INVALID_BEST_KNOWN_BLOCK_ERROR,
			"Invalid best known block",
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
			leaf_indices: vec![1],
			leaf_count: 9,
			items: vec![H256::repeat_byte(1), H256::repeat_byte(2)],
		};

		let leaf_proof = LeavesProof::new(H256::repeat_byte(0), vec![leaf], proof);

		// when
		let actual = serde_json::to_string(&leaf_proof).unwrap();

		// then
		assert_eq!(
			actual,
			r#"{"blockHash":"0x0000000000000000000000000000000000000000000000000000000000000000","leaves":"0x041001020304","proof":"0x04010000000000000009000000000000000801010101010101010101010101010101010101010101010101010101010101010202020202020202020202020202020202020202020202020202020202020202"}"#
		);
	}

	#[test]
	fn should_serialize_leaves_proof() {
		// given
		let leaf_a = vec![1_u8, 2, 3, 4];
		let leaf_b = vec![2_u8, 2, 3, 4];
		let proof = Proof {
			leaf_indices: vec![1, 2],
			leaf_count: 9,
			items: vec![H256::repeat_byte(1), H256::repeat_byte(2)],
		};

		let leaf_proof = LeavesProof::new(H256::repeat_byte(0), vec![leaf_a, leaf_b], proof);

		// when
		let actual = serde_json::to_string(&leaf_proof).unwrap();

		// then
		assert_eq!(
			actual,
			r#"{"blockHash":"0x0000000000000000000000000000000000000000000000000000000000000000","leaves":"0x0810010203041002020304","proof":"0x080100000000000000020000000000000009000000000000000801010101010101010101010101010101010101010101010101010101010101010202020202020202020202020202020202020202020202020202020202020202"}"#
		);
	}

	#[test]
	fn should_deserialize_leaf_proof() {
		// given
		let expected = LeavesProof {
			block_hash: H256::repeat_byte(0),
			leaves: Bytes(vec![vec![1_u8, 2, 3, 4]].encode()),
			proof: Bytes(
				Proof {
					leaf_indices: vec![1],
					leaf_count: 9,
					items: vec![H256::repeat_byte(1), H256::repeat_byte(2)],
				}
				.encode(),
			),
		};

		// when
		let actual: LeavesProof<H256> = serde_json::from_str(r#"{
			"blockHash":"0x0000000000000000000000000000000000000000000000000000000000000000",
			"leaves":"0x041001020304",
			"proof":"0x04010000000000000009000000000000000801010101010101010101010101010101010101010101010101010101010101010202020202020202020202020202020202020202020202020202020202020202"
		}"#).unwrap();

		// then
		assert_eq!(actual, expected);
	}

	#[test]
	fn should_deserialize_leaves_proof() {
		// given
		let expected = LeavesProof {
			block_hash: H256::repeat_byte(0),
			leaves: Bytes(vec![vec![1_u8, 2, 3, 4], vec![2_u8, 2, 3, 4]].encode()),
			proof: Bytes(
				Proof {
					leaf_indices: vec![1, 2],
					leaf_count: 9,
					items: vec![H256::repeat_byte(1), H256::repeat_byte(2)],
				}
				.encode(),
			),
		};

		// when
		let actual: LeavesProof<H256> = serde_json::from_str(r#"{
			"blockHash":"0x0000000000000000000000000000000000000000000000000000000000000000",
			"leaves":"0x0810010203041002020304",
			"proof":"0x080100000000000000020000000000000009000000000000000801010101010101010101010101010101010101010101010101010101010101010202020202020202020202020202020202020202020202020202020202020202"
		}"#).unwrap();

		// then
		assert_eq!(actual, expected);
	}
}
