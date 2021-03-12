// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Node-specific RPC methods for interaction with Merkle Mountain Range pallet.

use std::sync::Arc;

use codec::{Codec, Encode};
use jsonrpc_core::{Error, ErrorCode, Result};
use jsonrpc_derive::rpc;
use serde::{Deserialize, Serialize};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_core::Bytes;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT},
};
use pallet_mmr_primitives::{Error as MmrError, Proof};

pub use pallet_mmr_primitives::MmrApi as MmrRuntimeApi;

/// Retrieved MMR leaf and its proof.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct LeafProof<BlockHash> {
	/// Block hash the proof was generated for.
	pub block_hash: BlockHash,
	/// SCALE-encoded leaf data.
	pub leaf: Bytes,
	/// SCALE-encoded proof data. See [pallet_mmr_primitives::Proof].
	pub proof: Bytes,
}

impl<BlockHash> LeafProof<BlockHash> {
	/// Create new `LeafProof` from given concrete `leaf` and `proof`.
	pub fn new<Leaf, MmrHash>(
		block_hash: BlockHash,
		leaf: Leaf,
		proof: Proof<MmrHash>,
	) -> Self where
		Leaf: Encode,
		MmrHash: Encode,
	{
		Self {
			block_hash,
			leaf: Bytes(leaf.encode()),
			proof: Bytes(proof.encode()),
		}
	}
}

/// MMR RPC methods.
#[rpc]
pub trait MmrApi<BlockHash> {
	/// Generate MMR proof for given leaf index.
	///
	/// This method calls into a runtime with MMR pallet included and attempts to generate
	/// MMR proof for leaf at given `leaf_index`.
	/// Optionally, a block hash at which the runtime should be queried can be specified.
	///
	/// Returns the (full) leaf itself and a proof for this leaf (compact encoding, i.e. hash of
	/// the leaf). Both parameters are SCALE-encoded.
	#[rpc(name = "mmr_generateProof")]
	fn generate_proof(
		&self,
		leaf_index: u64,
		at: Option<BlockHash>,
	) -> Result<LeafProof<BlockHash>>;
}

/// An implementation of MMR specific RPC methods.
pub struct Mmr<C, B> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<B>,
}

impl<C, B> Mmr<C, B> {
	/// Create new `Mmr` with the given reference to the client.
	pub fn new(client: Arc<C>) -> Self {
		Self {
			client,
			_marker: Default::default(),
		}
	}
}

impl<C, Block, MmrHash> MmrApi<<Block as BlockT>::Hash,> for Mmr<C, (Block, MmrHash)>
where
	Block: BlockT,
	C: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	C::Api: MmrRuntimeApi<
		Block,
		MmrHash,
	>,
	MmrHash: Codec + Send + Sync + 'static,
{
	fn generate_proof(
		&self,
		leaf_index: u64,
		at: Option<<Block as BlockT>::Hash>,
	) -> Result<LeafProof<<Block as BlockT>::Hash>> {
		let api = self.client.runtime_api();
		let block_hash = at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash
		);

		let (leaf, proof) = api
			.generate_proof_with_context(
				&BlockId::hash(block_hash),
				sp_core::ExecutionContext::OffchainCall(None),
				leaf_index,
			)
			.map_err(runtime_error_into_rpc_error)?
			.map_err(mmr_error_into_rpc_error)?;

		Ok(LeafProof::new(block_hash, leaf, proof))
	}
}

const RUNTIME_ERROR: i64 = 8000;
const MMR_ERROR: i64 = 8010;

/// Converts a mmr-specific error into an RPC error.
fn mmr_error_into_rpc_error(err: MmrError) -> Error {
	match err {
		MmrError::LeafNotFound => Error {
			code: ErrorCode::ServerError(MMR_ERROR + 1),
			message: "Leaf was not found".into(),
			data: Some(format!("{:?}", err).into()),
		},
		MmrError::GenerateProof => Error {
			code: ErrorCode::ServerError(MMR_ERROR + 2),
			message: "Error while generating the proof".into(),
			data: Some(format!("{:?}", err).into()),
		},
		_ => Error {
			code: ErrorCode::ServerError(MMR_ERROR),
			message: "Unexpected MMR error".into(),
			data: Some(format!("{:?}", err).into()),
		},
	}
}

/// Converts a runtime trap into an RPC error.
fn runtime_error_into_rpc_error(err: impl std::fmt::Debug) -> Error {
	Error {
		code: ErrorCode::ServerError(RUNTIME_ERROR),
		message: "Runtime trapped".into(),
		data: Some(format!("{:?}", err).into()),
	}
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
	fn should_deserialize_leaf_proof() {
		// given
		let expected = LeafProof {
			block_hash: H256::repeat_byte(0),
			leaf: Bytes(vec![1_u8, 2, 3, 4].encode()),
			proof: Bytes(Proof {
				leaf_index: 1,
				leaf_count: 9,
				items: vec![H256::repeat_byte(1), H256::repeat_byte(2)],
			}.encode()),
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
}
