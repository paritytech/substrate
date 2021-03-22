// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Storge Proof Primitives

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::{result::Result, prelude::*};

use codec::{Encode, Decode};
use sp_inherents::{Error, InherentIdentifier, InherentData, IsFatalError};

/// The identifier for the proof inherent.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"tx_proof";
pub const STORAGE_PERIOD: u32 = 10;
pub const CHUNK_SIZE: usize = 256;

/// Errors that can occur while checking the storage proof.
#[derive(Encode, sp_runtime::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub enum InherentError {
	InvalidProof,
	TrieError
}

impl IsFatalError for InherentError {
	fn is_fatal_error(&self) -> bool {
		true
	}
}

#[derive(Encode, Decode, Clone, PartialEq, Debug)]
pub struct StorageProof {
	/// Data chunk that is proved to exist.
	pub chunk: Vec<u8>,
	/// Trie nodes that compose the proof.
	pub proof: Vec<Vec<u8>>,
}

/// Auxiliary trait to extract storage proof.
pub trait StorageProofInherentData {
	/// Get the proof.
	fn storage_proof(&self) -> Result<Option<StorageProof>, Error>;
}

impl StorageProofInherentData for InherentData {
	fn storage_proof(&self) -> Result<Option<StorageProof>, Error> {
		Ok(self.get_data(&INHERENT_IDENTIFIER)?)
	}
}

/// Provider for inherent data.
#[cfg(feature = "std")]
pub struct InherentDataProvider<F> {
	inner: F,
}

#[cfg(feature = "std")]
impl<F> InherentDataProvider<F> {
	pub fn new(proof_oracle: F) -> Self {
		InherentDataProvider { inner: proof_oracle }
	}
}

#[cfg(feature = "std")]
impl<F> sp_inherents::ProvideInherentData for InherentDataProvider<F>
where F: Fn() -> Result<Option<StorageProof>, Error>
{
	fn inherent_identifier(&self) -> &'static InherentIdentifier {
		&INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), Error> {
		let proof = (self.inner)()?;
		if let Some(proof) = proof {
			inherent_data.put_data(INHERENT_IDENTIFIER, &proof)
		} else {
			Ok(())
		}
	}

	fn error_to_string(&self, _error: &[u8]) -> Option<String> {
		Some(format!("no further information"))
	}
}


pub fn random_chunk(random_hash: &[u8], total_chunks: u32) -> u32 {
	let mut buf = [0u8; 8];
	buf.copy_from_slice(&random_hash[0..8]);
	let random_u64 = u64::from_be_bytes(buf);
	(random_u64 % total_chunks as u64) as u32
}

#[cfg(feature = "std")]
pub mod registration {
	use sp_consensus::SelectChain;
	use sp_inherents::{InherentDataProviders};
	use log::warn;
	use sc_client_api::{HeaderBackend, BlockBackend};
	use sp_runtime::{traits::{Block as BlockT, Header, Saturating, Zero}, generic::BlockId};
	use std::sync::Arc;
	use sp_trie::{TrieConfiguration, TrieMut};
	use crate::{StorageProof, CHUNK_SIZE};
	use std::iter::once;

	type TrieLayout = sp_trie::Layout::<Hasher>;
	type Hasher = sp_core::Blake2Hasher;


	/// Register uncles inherent data provider, if not registered already.
	pub fn register_storage_proof_inherent_data_provider<B, C, SC>(
		client: Arc<C>,
		select_chain: SC,
		inherent_data_providers: &InherentDataProviders,
	) -> Result<(), sp_consensus::Error> where
	B: BlockT,
	C: BlockBackend<B> + HeaderBackend<B> + Send + Sync + 'static,
	SC: SelectChain<B> + 'static,
	{
		if !inherent_data_providers.has_provider(&crate::INHERENT_IDENTIFIER) {
			inherent_data_providers
				.register_provider(crate::InherentDataProvider::new(move || {
					{
						let chain_head = match select_chain.best_chain() {
							Ok(x) => x,
							Err(e) => {
								warn!(target: "storage-proof", "Unable to get chain head: {:?}", e);
								return Ok(None);
							}
						};

						let number = chain_head.number().saturating_sub(crate::STORAGE_PERIOD.into());
						if number.is_zero() {
							// Too early to collect proofs.
							return Ok(None);
						}

						match client.block_indexed_body(&BlockId::number(number)) {
							Ok(Some(transactions)) => {
								Ok(Some(build_proof::<B>(chain_head.parent_hash().as_ref(), transactions)?))
							},
							Ok(None) => {
								// Nothing was indexed in that block.
								Ok(None)
							}
							Err(e) => {
								warn!(target: "storage-proof", "Unable to get transactions: {:?}", e);
								Ok(None)
							}
						}
					}
				}))
			.map_err(|err| sp_consensus::Error::InherentData(err.into()))?;
		}
		Ok(())
	}

	fn build_proof<B: BlockT>(random_hash: &[u8], transactions: Vec<Vec<u8>>)
		-> Result<StorageProof, sp_inherents::Error>
	{
		let mut block_root = sp_trie::empty_trie_root::<TrieLayout>();
		let mut db = sp_trie::MemoryDB::<Hasher>::default();

		let mut target_chunk = None;
		let mut target_root = Default::default();
		let mut target_chunk_key = Default::default();
		let mut target_block_key = Default::default();
		let mut chunk_proof = Default::default();

		let total_chunks: u64 = transactions.iter().map(|t| ((t.len() + CHUNK_SIZE - 1) / CHUNK_SIZE) as u64).sum();
		let mut buf = [0u8; 8];
		buf.copy_from_slice(&random_hash[0..8]);
		let random_u64 = u64::from_be_bytes(buf);
		let target_chunk_index = random_u64 % total_chunks;
		//Generate tries for each

		let mut chunk_index = 0;
		for (ti, transaction) in transactions.into_iter().enumerate() {
			let mut transaction_root = sp_trie::empty_trie_root::<TrieLayout>();
			{
				let mut trie = sp_trie::TrieDBMut::<TrieLayout>::new(&mut db, &mut transaction_root);
				let chunks = transaction.chunks(crate::CHUNK_SIZE).map(|c| c.to_vec());
				for (index, chunk) in chunks.enumerate() {
					let index = TrieLayout::encode_index(index as u32);
					trie.insert(&index, &chunk)
						.map_err(|e| sp_inherents::Error::from(format!("Trie error: {:?}", e)))?;
					if chunk_index == target_chunk_index {
						target_chunk = Some(chunk);
						target_chunk_key = index;
					}
					chunk_index += 1;
				}
				trie.commit();
			}
			let transaction_key = TrieLayout::encode_index(ti as u32);
			if target_chunk.is_some() && target_root == Default::default() {
				target_root = transaction_root.clone();
				target_block_key = transaction_key.clone();
				chunk_proof = sp_trie::generate_trie_proof::<TrieLayout, _, _, _>(
					&db,
					transaction_root.clone(),
					&[target_chunk_key.clone()]
				).map_err(|e| sp_inherents::Error::from(format!("Trie error: {:?}", e)))?;
			}
			{
				let mut block_trie = sp_trie::TrieDBMut::<TrieLayout>::new(&mut db, &mut block_root);
				block_trie.insert(&transaction_key, transaction_root.as_ref())
					.map_err(|e| sp_inherents::Error::from(format!("Trie error: {:?}", e)))?;
				block_trie.commit();
			}
		};
		let block_proof = sp_trie::generate_trie_proof::<TrieLayout, _, _, _>(
			&db,
			block_root,
			&[target_block_key]
		).map_err(|e| sp_inherents::Error::from(format!("Trie error: {:?}", e)))?;

		let proof = sp_trie::StorageProof::merge(
			once(sp_trie::StorageProof::new(chunk_proof)).chain(
				once(sp_trie::StorageProof::new(block_proof))));

		Ok(StorageProof {
			proof: proof.into_nodes(),
			chunk: target_chunk.unwrap(),
		})
	}
}
