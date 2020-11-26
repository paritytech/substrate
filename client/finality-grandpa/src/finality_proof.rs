// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! GRANDPA block finality proof generation and check.
//!
//! Finality of block B is proved by providing:
//! 1) the justification for the descendant block F;
//! 2) headers sub-chain (B; F] if B != F;
//! 3) proof of GRANDPA::authorities() if the set changes at block F.
//!
//! Since earliest possible justification is returned, the GRANDPA authorities set
//! at the block F is guaranteed to be the same as in the block B (this is because block
//! that enacts new GRANDPA authorities set always comes with justification). It also
//! means that the `set_id` is the same at blocks B and F.
//!
//! Let U be the last finalized block known to caller. If authorities set has changed several
//! times in the (U; F] interval, multiple finality proof fragments are returned (one for each
//! authority set change) and they must be verified in-order.
//!
//! Finality proof provider can choose how to provide finality proof on its own. The incomplete
//! finality proof (that finalizes some block C that is ancestor of the B and descendant
//! of the U) could be returned.

use std::sync::Arc;
use log::trace;

use sp_blockchain::{
	Backend as BlockchainBackend, Error as ClientError, Result as ClientResult,
};
use sc_client_api::{backend::Backend, StorageProvider, ProofProvider};
use parity_scale_codec::{Encode, Decode};
use finality_grandpa::BlockNumberOps;
use sp_runtime::{
	Justification, generic::BlockId,
	traits::{NumberFor, Block as BlockT, Header as HeaderT, One},
};
use sp_core::storage::StorageKey;
use sp_finality_grandpa::{AuthorityId, AuthorityList, VersionedAuthorityList, GRANDPA_AUTHORITIES_KEY};

use crate::justification::GrandpaJustification;
use crate::VoterSet;
use crate::SharedAuthoritySet;

pub trait AuthoritySetForFinalityProver<Block: BlockT>: Send + Sync {
	/// Read GRANDPA_AUTHORITIES_KEY from storage at given block.
	fn authorities(&self, block: &BlockId<Block>) -> ClientResult<AuthorityList>;
}

/// Trait that combines `StorageProvider` and `ProofProvider`
pub trait StorageAndProofProvider<Block, BE>:
	StorageProvider<Block, BE> + ProofProvider<Block> + Send + Sync
where
	Block: BlockT,
	BE: Backend<Block> + Send + Sync,
{}

/// Blanket implementation.
impl<Block, BE, P> StorageAndProofProvider<Block, BE> for P
where
	Block: BlockT,
	BE: Backend<Block> + Send + Sync,
	P: StorageProvider<Block, BE> + ProofProvider<Block> + Send + Sync,
{}

/// Implementation of AuthoritySetForFinalityProver.
impl<BE, Block: BlockT> AuthoritySetForFinalityProver<Block>
	for Arc<dyn StorageAndProofProvider<Block, BE>>
where
	BE: Backend<Block> + Send + Sync + 'static,
{
	fn authorities(&self, block: &BlockId<Block>) -> ClientResult<AuthorityList> {
		let storage_key = StorageKey(GRANDPA_AUTHORITIES_KEY.to_vec());
		self.storage(block, &storage_key)?
			.and_then(|encoded| VersionedAuthorityList::decode(&mut encoded.0.as_slice()).ok())
			.map(|versioned| versioned.into())
			.ok_or(ClientError::InvalidAuthoritiesSet)
	}
}
/// Finality proof provider for serving network requests.
pub struct FinalityProofProvider<B, Block: BlockT> {
	backend: Arc<B>,
	authority_provider: Arc<dyn AuthoritySetForFinalityProver<Block>>,
	shared_authority_set: Option<SharedAuthoritySet<Block::Hash, NumberFor<Block>>>,
}

impl<B, Block: BlockT> FinalityProofProvider<B, Block>
where
	B: Backend<Block> + Send + Sync + 'static,
{
	/// Create new finality proof provider using:
	///
	/// - backend for accessing blockchain data;
	/// - authority_provider for calling and proving runtime methods.
	pub fn new<P>(
		backend: Arc<B>,
		authority_provider: P,
		shared_authority_set: Option<SharedAuthoritySet<Block::Hash, NumberFor<Block>>>,
	) -> Self
	where
		P: AuthoritySetForFinalityProver<Block> + 'static,
	{
		FinalityProofProvider {
			backend,
			authority_provider: Arc::new(authority_provider),
			shared_authority_set,
		}
	}

	/// Create new finality proof provider for the service using:
	///
	/// - backend for accessing blockchain data;
	/// - storage_and_proof_provider, which is generally a client.
	pub fn new_for_service(
		backend: Arc<B>,
		storage_and_proof_provider: Arc<dyn StorageAndProofProvider<Block, B>>,
		shared_authority_set: Option<SharedAuthoritySet<Block::Hash, NumberFor<Block>>>,
	) -> Arc<Self> {
		Arc::new(Self::new(
			backend,
			storage_and_proof_provider,
			shared_authority_set,
		))
	}
}

impl<B, Block> FinalityProofProvider<B, Block>
where
	Block: BlockT,
	NumberFor<Block>: BlockNumberOps,
	B: Backend<Block> + Send + Sync + 'static,
{
	/// Prove finality for the given block number by returning a Justification for the last block of
	/// the authority set.
	pub fn prove_finality(&self, block: NumberFor<Block>) -> Result<Option<Vec<u8>>, ClientError> {
		let (set_id, last_block_for_set) = match self
			.shared_authority_set
			.as_ref()
			.map(SharedAuthoritySet::authority_set_changes)
			.and_then(|changes| changes.get_set_id(block))
		{
			Some((set_id, last_block_for_set)) => (set_id, last_block_for_set),
			None => return Ok(None),
		};

		prove_finality::<_, _, GrandpaJustification<Block>>(
			&*self.backend.blockchain(),
			&*self.authority_provider,
			set_id,
			block,
			last_block_for_set,
		)
	}
}

/// Finality for block B is proved by providing:
/// 1) the justification for the descendant block F;
/// 2) headers sub-chain (B; F] if B != F;
#[derive(Debug, PartialEq, Encode, Decode, Clone)]
pub struct FinalityProof<Header: HeaderT> {
	/// The hash of block F for which justification is provided.
	pub block: Header::Hash,
	/// Justification of the block F.
	pub justification: Vec<u8>,
	/// The set of headers in the range (B; F] that we believe are unknown to the caller. Ordered.
	pub unknown_headers: Vec<Header>,
}

fn prove_finality<Block: BlockT, B: BlockchainBackend<Block>, J>(
	blockchain: &B,
	authorities_provider: &dyn AuthoritySetForFinalityProver<Block>,
	authorities_set_id: u64,
	block: NumberFor<Block>,
	last_block_of_the_set: NumberFor<Block>,
) -> ::sp_blockchain::Result<Option<Vec<u8>>>
where
	J: ProvableJustification<Block::Header>,
{
	// Early-return if we sure that there are no blocks finalized AFTER begin block
	let info = blockchain.info();
	if info.finalized_number <= block {
		trace!(
			target: "afg",
			"Requested finality proof for descendant of #{} while we only have finalized #{}. Returning empty proof.",
			block,
			info.finalized_number,
		);
		return Ok(None);
	}

	let last_block_of_the_set_id = BlockId::Number(last_block_of_the_set);
	let last_block_of_the_set_hash =
		blockchain.expect_block_hash_from_id(&last_block_of_the_set_id)?;

	let justification =
		if let Some(justification) = blockchain.justification(last_block_of_the_set_id)? {
			justification
		} else {
			trace!(
				target: "afg",
				"No justification found when making finality proof for {}. Returning empty proof.",
				block,
			);
			return Ok(None);
		};

	let block_id = BlockId::Number(block);
	let block_authorities = authorities_provider.authorities(&block_id)?;

	// Check if the justification is generated by the requested authority set
	let justification_check_result =
		J::decode_and_verify(&justification, authorities_set_id, &block_authorities);
	if justification_check_result.is_err() {
		trace!(
			target: "afg",
			"Can not provide finality proof with requested set id #{}\
			(possible forced change?). Returning empty proof.",
			authorities_set_id,
		);
		return Ok(None);
	}

	// Get all headers from the requested block until the last block of the set
	let unknown_headers = {
		let mut unknown_headers = Vec::new();
		let mut current_number = block + One::one();
		let max_loop = current_number + 1000000.into(); // WIP(JON)
		loop {
			if current_number >= last_block_of_the_set || current_number >= max_loop {
				break;
			}

			let current_id = BlockId::Number(current_number);
			if block_authorities != authorities_provider.authorities(&current_id)? {
				trace!(
					target: "afg",
					"Encountered new authorities when collecting unknown headers. \
					Returning empty proof"
				);
				return Ok(None);
			}

			let unknown_header = blockchain.expect_header(current_id)?;
			unknown_headers.push(unknown_header);
			current_number += One::one();
		}
		unknown_headers
	};

	let finality_proof = FinalityProof {
		block: last_block_of_the_set_hash,
		justification,
		unknown_headers,
	};
	Ok(Some(finality_proof.encode()))
}

/// Check GRANDPA proof-of-finality for the given block.
///
/// Returns the vector of headers that MUST be validated + imported
/// AND if at least one of those headers is invalid, all other MUST be considered invalid.
///
/// This is currently not used, and exists primarily as an example of how to check finality proofs.
#[cfg(test)]
fn check_finality_proof<Header: HeaderT, J>(
	current_set_id: u64,
	current_authorities: AuthorityList,
	remote_proof: Vec<u8>,
) -> ClientResult<FinalityProof<Header>>
where
	J: ProvableJustification<Header>,
{
	let proof = FinalityProof::<Header>::decode(&mut &remote_proof[..])
		.map_err(|_| ClientError::BadJustification("failed to decode finality proof".into()))?;

	let justification: J = Decode::decode(&mut &proof.justification[..])
		.map_err(|_| ClientError::JustificationDecode)?;
	justification.verify(current_set_id, &current_authorities)?;

	use sc_telemetry::{telemetry, CONSENSUS_INFO};
	telemetry!(CONSENSUS_INFO; "afg.finality_proof_ok";
		"finalized_header_hash" => ?proof.block);
	Ok(proof)
}

/// Justification used to prove block finality.
trait ProvableJustification<Header: HeaderT>: Encode + Decode {
	/// Verify justification with respect to authorities set and authorities set id.
	fn verify(&self, set_id: u64, authorities: &[(AuthorityId, u64)]) -> ClientResult<()>;

	/// Decode and verify justification.
	fn decode_and_verify(
		justification: &Justification,
		set_id: u64,
		authorities: &[(AuthorityId, u64)],
	) -> ClientResult<Self> {
		let justification =
			Self::decode(&mut &**justification).map_err(|_| ClientError::JustificationDecode)?;
		justification.verify(set_id, authorities)?;
		Ok(justification)
	}
}

impl<Block: BlockT> ProvableJustification<Block::Header> for GrandpaJustification<Block>
where
	NumberFor<Block>: BlockNumberOps,
{
	fn verify(&self, set_id: u64, authorities: &[(AuthorityId, u64)]) -> ClientResult<()> {
		let authorities = VoterSet::new(authorities.iter().cloned()).ok_or(
			ClientError::Consensus(sp_consensus::Error::InvalidAuthoritiesSet),
		)?;

		GrandpaJustification::verify(self, set_id, &authorities)
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use super::*;
	use substrate_test_runtime_client::runtime::{Block, Header, H256};
	use sc_client_api::NewBlockState;
	use sc_client_api::in_mem::Blockchain as InMemoryBlockchain;
	use sp_core::crypto::Public;

	pub(crate) type FinalityProof = super::FinalityProof<Header>;

	impl<GetAuthorities> AuthoritySetForFinalityProver<Block> for GetAuthorities
	where
		GetAuthorities: Send + Sync + Fn(BlockId<Block>) -> ClientResult<AuthorityList>,
	{
		fn authorities(&self, block: &BlockId<Block>) -> ClientResult<AuthorityList> {
			self(*block)
		}
	}

	#[derive(Debug, PartialEq, Encode, Decode)]
	pub struct TestJustification(pub (u64, AuthorityList), pub Vec<u8>);

	impl ProvableJustification<Header> for TestJustification {
		fn verify(&self, set_id: u64, authorities: &[(AuthorityId, u64)]) -> ClientResult<()> {
			if (self.0).0 != set_id || (self.0).1 != authorities {
				return Err(ClientError::BadJustification("test".into()));
			}

			Ok(())
		}
	}

	fn header(number: u64) -> Header {
		let parent_hash = match number {
			0 => Default::default(),
			_ => header(number - 1).hash(),
		};
		Header::new(
			number,
			H256::from_low_u64_be(0),
			H256::from_low_u64_be(0),
			parent_hash,
			Default::default(),
		)
	}

	fn test_blockchain() -> InMemoryBlockchain<Block> {
		let blockchain = InMemoryBlockchain::<Block>::new();
		blockchain
			.insert(header(0).hash(), header(0), Some(vec![0]), None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(1).hash(), header(1), Some(vec![1]), None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(2).hash(), header(2), None, None, NewBlockState::Best)
			.unwrap();
		blockchain
			.insert(header(3).hash(), header(3), Some(vec![3]), None, NewBlockState::Final)
			.unwrap();
		blockchain
	}

	#[test]
	fn finality_proof_is_none_if_no_more_last_finalized_blocks() {
		let blockchain = test_blockchain();
		blockchain
			.insert(header(4).hash(), header(4), None, None, NewBlockState::Best)
			.unwrap();

		// our last finalized is: 3
		// their last finalized is: 3
		// => we can't provide any additional justifications
		let proof_of_4 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|_| unreachable!("should return before calling GetAuthorities"),
			0,
			*header(3).number(),
			*header(4).number(),
		)
		.unwrap();
		assert_eq!(proof_of_4, None);
	}

	#[test]
	fn finality_proof_is_none_if_no_justification_known() {
		let blockchain = test_blockchain();
		blockchain
			.insert(header(4).hash(), header(4), None, None, NewBlockState::Final)
			.unwrap();

		// block 4 is finalized without justification
		// => we can't prove finality
		let proof_of_4 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|_| unreachable!("should return before calling GetAuthorities"),
			0,
			*header(3).number(),
			*header(4).number(),
		)
		.unwrap();
		assert_eq!(proof_of_4, None);
	}

	#[test]
	fn finality_proof_works_for_basic_setup() {
		let blockchain = test_blockchain();
		let authorities = vec![(AuthorityId::from_slice(&[1u8; 32]), 1u64)];
		let just4 = TestJustification((0, authorities.clone()), vec![4]).encode();
		let just5 = TestJustification((0, authorities.clone()), vec![5]).encode();
		blockchain
			.insert(header(4).hash(), header(4), Some(just4), None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(5).hash(), header(5), Some(just5.clone()), None, NewBlockState::Final)
			.unwrap();

		// Blocks 4 && 5 are finalized with justification
		let proof_of_5: FinalityProof = Decode::decode(
			&mut &prove_finality::<_, _, TestJustification>(
				&blockchain,
				&|_| Ok(authorities.clone()),
				0,
				*header(3).number(),
				*header(5).number(),
			)
			.unwrap()
			.unwrap()[..],
		)
		.unwrap();
		assert_eq!(
			proof_of_5,
			FinalityProof {
				block: header(5).hash(),
				justification: just5,
				unknown_headers: vec![header(4)],
			}
		);

		// Now let's verify finality proof
		let blockchain = test_blockchain();
		blockchain
			.insert(header(4).hash(), header(4), None, None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(5).hash(), header(5), None, None, NewBlockState::Final)
			.unwrap();
		let proof = check_finality_proof::<_, TestJustification>(
			0,
			authorities.clone(),
			proof_of_5.encode(),
		)
		.unwrap();

		assert_eq!(proof, proof_of_5);
	}

	#[test]
	fn finality_proof_check_fails_when_proof_decode_fails() {
		// when we can't decode proof from Vec<u8>
		check_finality_proof::<_, TestJustification>(
			1,
			vec![(AuthorityId::from_slice(&[3u8; 32]), 1u64)],
			vec![42],
		)
		.unwrap_err();
	}

	#[test]
	fn finality_proof_check_fails_when_proof_is_empty() {
		// when decoded proof has zero length
		check_finality_proof::<_, TestJustification>(
			1,
			vec![(AuthorityId::from_slice(&[3u8; 32]), 1u64)],
			Vec::<TestJustification>::new().encode(),
		)
		.unwrap_err();
	}

	#[test]
	fn finality_proof_check_works() {
		let initial_authorities = vec![(AuthorityId::from_slice(&[3u8; 32]), 1u64)];
		let finality_proof = FinalityProof {
			block: header(2).hash(),
			justification: TestJustification((1, initial_authorities.clone()), vec![7]).encode(),
			unknown_headers: Vec::new(),
		};
		let proof = check_finality_proof::<_, TestJustification>(
			1,
			initial_authorities.clone(),
			finality_proof.encode(),
		)
		.unwrap();
		assert_eq!(proof, finality_proof);
	}

	#[test]
	fn finality_proof_is_none_if_justification_is_generated_by_unknown_set() {
		// This is the case for forced change: set_id has been forcibly increased,
		// or when our stored authority set changes is incomplete
		let blockchain = test_blockchain();
		let just4 = TestJustification(
			(0, vec![(AuthorityId::from_slice(&[42u8; 32]), 1u64)]),
			vec![4],
		)
		.encode();
		blockchain
			.insert(header(4).hash(), header(4), Some(just4), None, NewBlockState::Final)
			.unwrap();

		let proof_of_3 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|_| Ok(vec![(AuthorityId::from_slice(&[1u8; 32]), 1u64)]),
			0,
			*header(3).number(),
			*header(4).number(),
		)
		.unwrap();
		assert!(proof_of_3.is_none());
	}

	#[test]
	fn finality_proof_is_none_if_authority_set_id_is_incorrect() {
		let blockchain = test_blockchain();
		let just4 = TestJustification(
			(0, vec![(AuthorityId::from_slice(&[1u8; 32]), 1u64)]),
			vec![4],
		)
		.encode();
		blockchain
			.insert(header(4).hash(), header(4), Some(just4), None, NewBlockState::Final)
			.unwrap();

		// We call `prove_finality` with the wrong `authorities_set_id`, since the Justification for
		// block 4 contains set id 0.
		let proof_of_3 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|_| Ok(vec![(AuthorityId::from_slice(&[1u8; 32]), 1u64)]),
			1,
			*header(3).number(),
			*header(4).number(),
		)
		.unwrap();
		assert!(proof_of_3.is_none());
	}

	#[test]
	fn finality_proof_is_none_for_next_set_id_with_same_authorities() {
		let blockchain = test_blockchain();
		let auth = vec![(AuthorityId::from_slice(&[1u8; 32]), 1u64)];
		let just5 = TestJustification((0, auth.clone()), vec![5]).encode();
		let just6 = TestJustification((1, auth.clone()), vec![6]).encode();
		blockchain
			.insert(header(4).hash(), header(4), None, None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(5).hash(), header(5), Some(just5), None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(6).hash(), header(6), Some(just6), None, NewBlockState::Final)
			.unwrap();

		// Try to prove finality from the next set_id, but which has the same authorities.
		let proof_of_4 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|_| Ok(auth.clone()),
			1,
			*header(4).number(),
			*header(6).number(),
		)
		.unwrap();
		// WIP(JON): Currently this test fails, as the different set_id isn't detected.
		assert!(proof_of_4.is_none());
	}

	#[test]
	fn finality_proof_is_none_for_next_set_id_with_new_the_authority_set() {
		let blockchain = test_blockchain();
		let auth1 = vec![(AuthorityId::from_slice(&[1u8; 32]), 1u64)];
		let auth2 = vec![(AuthorityId::from_slice(&[2u8; 32]), 1u64)];
		let just5 = TestJustification((0, auth1.clone()), vec![5]).encode();
		let just6 = TestJustification((1, auth2.clone()), vec![6]).encode();
		blockchain
			.insert(header(4).hash(), header(4), None, None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(5).hash(), header(5), Some(just5), None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(6).hash(), header(6), Some(just6), None, NewBlockState::Final)
			.unwrap();

		let proof_of_4 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|block_id| match block_id {
				BlockId::Number(4) => Ok(auth1.clone()),
				BlockId::Number(5) => Ok(auth1.clone()),
				BlockId::Number(6) => Ok(auth2.clone()),
				_ => unimplemented!("No other authorities should be proved: {:?}", block_id),
			},
			1,
			*header(4).number(),
			*header(6).number(),
		)
		.unwrap();
		assert!(proof_of_4.is_none());
	}

	#[test]
	fn finality_proof_is_none_if_the_authority_set_changes_and_changes_back() {
		let blockchain = test_blockchain();
		let auth1 = vec![(AuthorityId::from_slice(&[1u8; 32]), 1u64)];
		let auth2 = vec![(AuthorityId::from_slice(&[2u8; 32]), 1u64)];
		let just5 = TestJustification((0, auth1.clone()), vec![5]).encode();
		let just6 = TestJustification((1, auth2.clone()), vec![6]).encode();
		let just7 = TestJustification((2, auth1.clone()), vec![7]).encode();
		blockchain
			.insert(header(4).hash(), header(4), None, None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(5).hash(), header(5), Some(just5), None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(6).hash(), header(6), Some(just6), None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(7).hash(), header(7), Some(just7), None, NewBlockState::Final)
			.unwrap();

		// Try to prove finality using a later set_id than the block we're trying to prove, but
		// that has the same authorities.
		let proof_of_4 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|block_id| match block_id {
				BlockId::Number(4) => Ok(auth1.clone()),
				BlockId::Number(5) => Ok(auth1.clone()),
				BlockId::Number(6) => Ok(auth2.clone()),
				BlockId::Number(7) => Ok(auth1.clone()),
				_ => unimplemented!("No other authorities should be proved: {:?}", block_id),
			},
			2,
			*header(4).number(),
			*header(7).number(),
		)
		.unwrap();
		assert!(proof_of_4.is_none());
	}
}
