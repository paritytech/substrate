// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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
use sc_client_api::{backend::Backend, StorageProvider};
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
use crate::authorities::AuthoritySetChanges;

const MAX_UNKNOWN_HEADERS: usize = 100_000;

pub trait AuthoritySetForFinalityProver<Block: BlockT>: Send + Sync {
	/// Read GRANDPA_AUTHORITIES_KEY from storage at given block.
	fn authorities(&self, block: &BlockId<Block>) -> ClientResult<AuthorityList>;
}

/// Implementation of AuthoritySetForFinalityProver.
impl<BE, Block: BlockT> AuthoritySetForFinalityProver<Block>
	for Arc<dyn StorageProvider<Block, BE> + Send + Sync>
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
pub struct FinalityProofProvider<BE, Block: BlockT> {
	backend: Arc<BE>,
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
	/// - shared_authority_set for accessing authority set data
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
	/// - storage_provider, which is generally a client.
	/// - shared_authority_set for accessing authority set data
	pub fn new_for_service(
		backend: Arc<B>,
		storage_provider: Arc<dyn StorageProvider<Block, B> + Send + Sync>,
		shared_authority_set: Option<SharedAuthoritySet<Block::Hash, NumberFor<Block>>>,
	) -> Arc<Self> {
		Arc::new(Self::new(
			backend,
			storage_provider,
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
	pub fn prove_finality(&self, block: NumberFor<Block>)
		-> Result<Option<Vec<u8>>, FinalityProofError>
	{
		let authority_set_changes = if let Some(changes) = self
			.shared_authority_set
			.as_ref()
			.map(SharedAuthoritySet::authority_set_changes)
		{
			changes
		} else {
			return Ok(None);
		};

		prove_finality::<_, _, GrandpaJustification<Block>>(
			&*self.backend.blockchain(),
			&*self.authority_provider,
			authority_set_changes,
			block,
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

/// Errors occurring when trying to prove finality
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum FinalityProofError {
	/// The requested block has not yet been finalized.
	#[display(fmt = "Block not yet finalized")]
	BlockNotYetFinalized,
	/// The requested block is not covered by authority set changes. Likely this means the block is
	/// in the latest authority set, and the subscription API is more appropriate.
	#[display(fmt = "Block not covered by authority set changes")]
	BlockNotInAuthoritySetChanges,
	/// Errors originating from the client.
	Client(sp_blockchain::Error),
}

fn prove_finality<Block, B, J>(
	blockchain: &B,
	authorities_provider: &dyn AuthoritySetForFinalityProver<Block>,
	authority_set_changes: AuthoritySetChanges<NumberFor<Block>>,
	block: NumberFor<Block>,
) -> Result<Option<Vec<u8>>, FinalityProofError>
where
	Block: BlockT,
	B: BlockchainBackend<Block>,
	J: ProvableJustification<Block::Header>,
{
	// Early-return if we sure that there are no blocks finalized AFTER begin block
	let info = blockchain.info();
	if info.finalized_number <= block {
		let err = format!(
			"Requested finality proof for descendant of #{} while we only have finalized #{}.",
			block,
			info.finalized_number,
		);
		trace!(target: "afg", "{}", &err);
		return Err(FinalityProofError::BlockNotYetFinalized);
	}

	// Get set_id the block belongs to, and the last block of the set which should contain a
	// Justification we can use to prove the requested block.
	let (set_id, last_block_for_set) = if let Some(id) = authority_set_changes.get_set_id(block) {
		id
	} else {
		trace!(
			target: "afg",
			"AuthoritySetChanges does not cover the requested block #{}. \
			Maybe the subscription API is more appropriate.",
			block,
		);
		return Err(FinalityProofError::BlockNotInAuthoritySetChanges);
	};

	// Get the Justification stored at the last block of the set
	let last_block_for_set_id = BlockId::Number(last_block_for_set);
	let justification =
		if let Some(justification) = blockchain.justification(last_block_for_set_id)? {
			justification
		} else {
			trace!(
				target: "afg",
				"No justification found when making finality proof for {}. Returning empty proof.",
				block,
			);
			return Ok(None);
		};


	// Check if the justification is generated by the requested authority set
	let block_authorities = authorities_provider.authorities(&BlockId::Number(block))?;
	let justification_check_result =
		J::decode_and_verify(&justification, set_id, &block_authorities);
	if justification_check_result.is_err() {
		trace!(
			target: "afg",
			"Can not provide finality proof with requested set id #{}\
			(possible forced change?). Returning empty proof.",
			set_id,
		);
		return Ok(None);
	}

	// Collect all headers from the requested block until the last block of the set
	let unknown_headers = {
		let mut headers = Vec::new();
		let mut current = block + One::one();
		loop {
			if current >= last_block_for_set || headers.len() >= MAX_UNKNOWN_HEADERS {
				break;
			}
			if block_authorities != authorities_provider.authorities(&BlockId::Number(current))? {
				trace!(
					target: "afg",
					"Encountered new authorities when collecting unknown headers. \
					Returning empty proof",
				);
				return Ok(None);
			}
			headers.push(blockchain.expect_header(BlockId::Number(current))?);
			current += One::one();
		}
		headers
	};

	Ok(Some(
		FinalityProof {
			block: blockchain.expect_block_hash_from_id(&last_block_for_set_id)?,
			justification,
			unknown_headers,
		}
		.encode(),
	))
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
	use crate::authorities::AuthoritySetChanges;

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
			.insert(header(4).hash(), header(4), Some(vec![1]), None, NewBlockState::Best)
			.unwrap();
		blockchain
			.insert(header(5).hash(), header(5), Some(vec![2]), None, NewBlockState::Best)
			.unwrap();

		let mut authority_set_changes = AuthoritySetChanges::empty();
		authority_set_changes.append(0, 5);

		// The last finalized block is 3, so we cannot provide further justifications.
		let proof_of_4 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|_| unreachable!("Should return before calling GetAuthorities"),
			authority_set_changes,
			*header(4).number(),
		);
		assert!(matches!(proof_of_4, Err(FinalityProofError::BlockNotYetFinalized)));
	}

	#[test]
	fn finality_proof_is_none_if_no_justification_known() {
		let blockchain = test_blockchain();
		blockchain
			.insert(header(4).hash(), header(4), None, None, NewBlockState::Final)
			.unwrap();

		let mut authority_set_changes = AuthoritySetChanges::empty();
		authority_set_changes.append(0, 4);

		// Block 4 is finalized without justification
		// => we can't prove finality of 3
		let proof_of_3 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|_| unreachable!("Should return before calling GetAuthorities"),
			authority_set_changes,
			*header(3).number(),
		)
		.unwrap();
		assert_eq!(proof_of_3, None);
	}

	#[test]
	fn finality_proof_is_none_if_justification_is_generated_by_unknown_set() {
		// This is the case for forced change: set_id has been forcibly increased,
		// or when our stored authority set changes is incomplete
		let blockchain = test_blockchain();
		let auth = vec![(AuthorityId::from_slice(&[42u8; 32]), 1u64)];
		let just4 = TestJustification((0, auth), vec![4]).encode();
		blockchain
			.insert(header(4).hash(), header(4), Some(just4), None, NewBlockState::Final)
			.unwrap();

		let mut authority_set_changes = AuthoritySetChanges::empty();
		authority_set_changes.append(0, 4);

		let proof_of_3 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|_| Ok(vec![(AuthorityId::from_slice(&[1u8; 32]), 1u64)]),
			authority_set_changes,
			*header(3).number(),
		)
		.unwrap();
		assert!(proof_of_3.is_none());
	}

	#[test]
	fn finality_proof_is_none_if_authority_set_id_is_incorrect() {
		let blockchain = test_blockchain();
		let auth = vec![(AuthorityId::from_slice(&[1u8; 32]), 1u64)];
		let just4 = TestJustification((0, auth.clone()), vec![4]).encode();
		blockchain
			.insert(header(4).hash(), header(4), Some(just4), None, NewBlockState::Final)
			.unwrap();

		let mut authority_set_changes = AuthoritySetChanges::empty();
		authority_set_changes.append(0, 1);
		authority_set_changes.append(1, 4);

		// We call `prove_finality` with the wrong `authorities_set_id`, since the Justification for
		// block 4 contains set id 0.
		let proof_of_3 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|_| Ok(auth.clone()),
			authority_set_changes,
			*header(3).number(),
		)
		.unwrap();
		assert!(proof_of_3.is_none());
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

		let mut authority_set_changes = AuthoritySetChanges::empty();
		authority_set_changes.append(0, 1);
		authority_set_changes.append(1, 6);

		// Trying to prove block 4 using block 6 fails as the authority set has changed
		let proof_of_4 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|block_id| match block_id {
				BlockId::Number(4) => Ok(auth1.clone()),
				_ => unimplemented!("No other authorities should be proved: {:?}", block_id),
			},
			authority_set_changes,
			*header(4).number(),
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

		// Set authority set changes so that they don't contain the switch, and switch back, of the
		// authorities. As well as incorrect set_id to avoid the guard against that.
		// This should trigger the check for walking through the headers and checking for authority
		// set changes that are missed.
		let mut authority_set_changes = AuthoritySetChanges::empty();
		authority_set_changes.append(0, 1);
		authority_set_changes.append(1, 2);
		authority_set_changes.append(2, 7);

		let proof_of_4 =
			prove_finality::<_, _, TestJustification>(
				&blockchain,
				&|block_id| match block_id {
					BlockId::Number(4) => Ok(auth1.clone()),
					BlockId::Number(5) => Ok(auth1.clone()),
					BlockId::Number(6) => Ok(auth2.clone()),
					_ => unimplemented!("No other authorities should be proved: {:?}", block_id),
				},
				authority_set_changes,
				*header(4).number(),
			)
		.unwrap();
		assert!(proof_of_4.is_none());
	}

	#[test]
	fn finality_proof_check_fails_when_proof_decode_fails() {
		// When we can't decode proof from Vec<u8>
		check_finality_proof::<_, TestJustification>(
			1,
			vec![(AuthorityId::from_slice(&[3u8; 32]), 1u64)],
			vec![42],
		)
		.unwrap_err();
	}

	#[test]
	fn finality_proof_check_fails_when_proof_is_empty() {
		// When decoded proof has zero length
		check_finality_proof::<_, TestJustification>(
			1,
			vec![(AuthorityId::from_slice(&[3u8; 32]), 1u64)],
			Vec::<TestJustification>::new().encode(),
		)
		.unwrap_err();
	}

	#[test]
	fn finality_proof_check_works() {
		let auth = vec![(AuthorityId::from_slice(&[3u8; 32]), 1u64)];
		let finality_proof = FinalityProof {
			block: header(2).hash(),
			justification: TestJustification((1, auth.clone()), vec![7]).encode(),
			unknown_headers: Vec::new(),
		};
		let proof = check_finality_proof::<_, TestJustification>(
			1,
			auth.clone(),
			finality_proof.encode(),
		)
		.unwrap();
		assert_eq!(proof, finality_proof);
	}

	#[test]
	fn finality_proof_using_authority_set_changes_is_none_with_undefined_start() {
		let blockchain = test_blockchain();
		let auth = vec![(AuthorityId::from_slice(&[1u8; 32]), 1u64)];
		let just4 = TestJustification((0, auth.clone()), vec![4]).encode();
		let just7 = TestJustification((1, auth.clone()), vec![7]).encode();
		blockchain
			.insert(header(4).hash(), header(4), Some(just4), None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(5).hash(), header(5), None, None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(6).hash(), header(6), None, None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(7).hash(), header(7), Some(just7.clone()), None, NewBlockState::Final)
			.unwrap();

		// We have stored the correct block number for the relevant set, but as we are missing the
		// block for the preceding set the start is not well-defined.
		let mut authority_set_changes = AuthoritySetChanges::empty();
		authority_set_changes.append(1, 7);

		let proof_of_5 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&|block_id| match block_id {
				BlockId::Number(5) => Ok(auth.clone()),
				BlockId::Number(6) => Ok(auth.clone()),
				_ => unimplemented!("No other authorities should be proved: {:?}", block_id),
			},
			authority_set_changes,
			*header(5).number(),
		);
		assert!(matches!(proof_of_5, Err(FinalityProofError::BlockNotInAuthoritySetChanges)));
	}

	#[test]
	fn finality_proof_using_authority_set_changes_works() {
		let blockchain = test_blockchain();
		let auth = vec![(AuthorityId::from_slice(&[1u8; 32]), 1u64)];
		let just4 = TestJustification((0, auth.clone()), vec![4]).encode();
		let just7 = TestJustification((1, auth.clone()), vec![7]).encode();
		blockchain
			.insert(header(4).hash(), header(4), Some(just4), None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(5).hash(), header(5), None, None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(6).hash(), header(6), None, None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(7).hash(), header(7), Some(just7.clone()), None, NewBlockState::Final)
			.unwrap();

		let mut authority_set_changes = AuthoritySetChanges::empty();
		authority_set_changes.append(0, 4);
		authority_set_changes.append(1, 7);

		let proof_of_5: FinalityProof = Decode::decode(
			&mut &prove_finality::<_, _, TestJustification>(
				&blockchain,
				&|block_id| match block_id {
					BlockId::Number(5) => Ok(auth.clone()),
					BlockId::Number(6) => Ok(auth.clone()),
					_ => unimplemented!("No other authorities should be proved: {:?}", block_id),
				},
				authority_set_changes,
				*header(5).number(),
			)
			.unwrap()
			.unwrap()[..],
		)
		.unwrap();
		assert_eq!(
			proof_of_5,
			FinalityProof {
				block: header(7).hash(),
				justification: just7,
				unknown_headers: vec![header(6)],
			}
		);
	}
}
