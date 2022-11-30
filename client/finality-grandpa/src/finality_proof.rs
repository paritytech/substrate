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

use log::trace;
use std::sync::Arc;

use finality_grandpa::BlockNumberOps;
use parity_scale_codec::{Encode, Decode};
use sp_blockchain::{Backend as BlockchainBackend, Error as ClientError, Result as ClientResult};
use sp_runtime::{
	Justification, generic::BlockId,
	traits::{NumberFor, Block as BlockT, Header as HeaderT, Zero, One},
};
use sc_client_api::backend::Backend;
use sp_finality_grandpa::{AuthorityId, AuthorityList};

use crate::authorities::AuthoritySetChanges;
use crate::justification::GrandpaJustification;
use crate::SharedAuthoritySet;
use crate::VoterSet;

const MAX_UNKNOWN_HEADERS: usize = 100_000;

/// Finality proof provider for serving network requests.
pub struct FinalityProofProvider<BE, Block: BlockT> {
	backend: Arc<BE>,
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
	pub fn new(
		backend: Arc<B>,
		shared_authority_set: Option<SharedAuthoritySet<Block::Hash, NumberFor<Block>>>,
	) -> Self {
		FinalityProofProvider {
			backend,
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
		shared_authority_set: Option<SharedAuthoritySet<Block::Hash, NumberFor<Block>>>,
	) -> Arc<Self> {
		Arc::new(Self::new(backend, shared_authority_set))
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
	pub fn prove_finality(
		&self,
		block: NumberFor<Block>
	) -> Result<Option<Vec<u8>>, FinalityProofError> {
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

/// Single fragment of authority set proof.
///
/// Finality for block B is proved by providing:
/// 1) headers of this block;
/// 2) the justification for the block containing a authority set change digest;
#[derive(Debug, PartialEq, Clone, Encode, Decode)]
pub(crate) struct AuthoritySetProofFragment<Header: HeaderT> {
	/// The header of the given block.
	pub header: Header,
	/// Justification of the block F.
	pub justification: Vec<u8>,
}

/// Proof of authority set is the ordered set of authority set fragments, where:
/// - last fragment match target block.
type AuthoritySetProof<Header> = Vec<AuthoritySetProofFragment<Header>>;

fn prove_finality<Block, B, J>(
	blockchain: &B,
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
	let (_, last_block_for_set) = if let Some(id) = authority_set_changes.get_set_id(block) {
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

	// Collect all headers from the requested block until the last block of the set
	let unknown_headers = {
		let mut headers = Vec::new();
		let mut current = block + One::one();
		loop {
			if current >= last_block_for_set || headers.len() >= MAX_UNKNOWN_HEADERS {
				break;
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

/// Prepare authority proof for the best possible block starting at a given trusted block.
///
/// Started block should be in range of bonding duration.
/// We only return proof for finalized blocks (with justification).
///
/// It is assumed that the caller already have a proof-of-finality for the block 'begin'.
pub fn prove_warp_sync<Block: BlockT, B: BlockchainBackend<Block>>(
	blockchain: &B,
	begin: Block::Hash,
	max_fragment_limit: Option<usize>,
	mut cache: Option<&mut WarpSyncFragmentCache<Block::Header>>,
) -> ::sp_blockchain::Result<Vec<u8>> {

	let begin = BlockId::Hash(begin);
	let begin_number = blockchain.block_number_from_id(&begin)?
		.ok_or_else(|| ClientError::Backend("Missing start block".to_string()))?;
	let end = BlockId::Hash(blockchain.last_finalized()?);
	let end_number = blockchain.block_number_from_id(&end)?
		// This error should not happen, we could also panic.
		.ok_or_else(|| ClientError::Backend("Missing last finalized block".to_string()))?;

	if begin_number > end_number {
		return Err(ClientError::Backend("Unfinalized start for authority proof".to_string()));
	}

	let mut result = Vec::new();
	let mut last_apply = None;

	let header = blockchain.expect_header(begin)?;
	let mut index = *header.number();

	// Find previous change in case there is a delay.
	// This operation is a costy and only for the delay corner case.
	while index > Zero::zero() {
		index = index - One::one();
		if let Some((fragment, apply_block)) = get_warp_sync_proof_fragment(blockchain, index, &mut cache)? {
			if last_apply.map(|next| &next > header.number()).unwrap_or(false) {
				result.push(fragment);
				last_apply = Some(apply_block);
			} else {
				break;
			}
		}
	}

	let mut index = *header.number();
	while index <= end_number {
		if max_fragment_limit.map(|limit| result.len() >= limit).unwrap_or(false) {
			break;
		}

		if let Some((fragement, apply_block)) = get_warp_sync_proof_fragment(blockchain, index, &mut cache)? {
			if last_apply.map(|next| apply_block < next).unwrap_or(false) {
				// Previous delayed will not apply, do not include it.
				result.pop();
			}
			result.push(fragement);
			last_apply = Some(apply_block);
		}

		index = index + One::one();
	}

	let at_limit = max_fragment_limit.map(|limit| result.len() >= limit).unwrap_or(false);

	// add last finalized block if reached and not already included.
	if !at_limit && result.last().as_ref().map(|head| head.header.number()) != Some(&end_number) {
		let header = blockchain.expect_header(end)?;
		if let Some(justification) = blockchain.justification(BlockId::Number(end_number.clone()))? {
			result.push(AuthoritySetProofFragment {
				header: header.clone(),
				justification,
			});
		} else {
			// no justification, don't include it.
		}
	}

	Ok(result.encode())
}

/// Try get a warp sync proof fragment a a given finalized block.
fn get_warp_sync_proof_fragment<Block: BlockT, B: BlockchainBackend<Block>>(
	blockchain: &B,
	index: NumberFor<Block>,
	cache: &mut Option<&mut WarpSyncFragmentCache<Block::Header>>,
) -> sp_blockchain::Result<Option<(AuthoritySetProofFragment<Block::Header>, NumberFor<Block>)>> {
	if let Some(cache) = cache.as_mut() {
		if let Some(result) = cache.get_item(index) {
			return Ok(result);
		}
	}

	let mut result = None;
	let header = blockchain.expect_header(BlockId::number(index))?;

	if let Some((block_number, sp_finality_grandpa::ScheduledChange {
		next_authorities: _,
		delay,
	})) = crate::import::find_forced_change::<Block>(&header) {
		let dest = block_number + delay;
		if let Some(justification) = blockchain.justification(BlockId::Number(index.clone()))? {
			result = Some((AuthoritySetProofFragment {
				header: header.clone(),
				justification,
			}, dest));
		} else {
			return Err(ClientError::Backend("Unjustified block with authority set change".to_string()));
		}
	}

	if let Some(sp_finality_grandpa::ScheduledChange {
		next_authorities: _,
		delay,
	}) = crate::import::find_scheduled_change::<Block>(&header) {
		let dest = index + delay;
		if let Some(justification) = blockchain.justification(BlockId::Number(index.clone()))? {
			result = Some((AuthoritySetProofFragment {
				header: header.clone(),
				justification,
			}, dest));
		} else {
			return Err(ClientError::Backend("Unjustified block with authority set change".to_string()));
		}
	}

	cache.as_mut().map(|cache| cache.new_item(index, result.clone()));
	Ok(result)
}

/// Check GRANDPA authority change sequence to assert finality of a target block.
///
/// Returns the header of the target block.
#[allow(unused)]
pub(crate) fn check_warp_sync_proof<Block: BlockT, J>(
	current_set_id: u64,
	current_authorities: AuthorityList,
	remote_proof: Vec<u8>,
) -> ClientResult<(Block::Header, u64, AuthorityList)>
where
		NumberFor<Block>: BlockNumberOps,
		J: Decode + ProvableJustification<Block::Header> + BlockJustification<Block::Header>,
{
	// decode finality proof
	let proof = AuthoritySetProof::<Block::Header>::decode(&mut &remote_proof[..])
		.map_err(|_| ClientError::BadJustification("failed to decode authority proof".into()))?;

		let last = proof.len() - 1;

		let mut result = (current_set_id, current_authorities, NumberFor::<Block>::zero());

		for (ix, fragment) in proof.into_iter().enumerate() {
			let is_last = ix == last;
			result = check_warp_sync_proof_fragment::<Block, J>(
				result.0,
				&result.1,
				&result.2,
				is_last,
				&fragment,
			)?;

			if is_last {
				return Ok((fragment.header, result.0, result.1))
			}
		}

		// empty proof can't prove anything
		return Err(ClientError::BadJustification("empty proof of authority".into()));
}

/// Check finality authority set sequence.
fn check_warp_sync_proof_fragment<Block: BlockT, J>(
	current_set_id: u64,
	current_authorities: &AuthorityList,
	previous_checked_block: &NumberFor<Block>,
	is_last: bool,
	authorities_proof: &AuthoritySetProofFragment<Block::Header>,
) -> ClientResult<(u64, AuthorityList, NumberFor<Block>)>
where
		NumberFor<Block>: BlockNumberOps,
		J: Decode + ProvableJustification<Block::Header> + BlockJustification<Block::Header>,
{
	let justification: J = Decode::decode(&mut authorities_proof.justification.as_slice())
		.map_err(|_| ClientError::JustificationDecode)?;
		justification.verify(current_set_id, &current_authorities)?;

		// assert justification is for this header
		if &justification.number() != authorities_proof.header.number()
			|| justification.hash().as_ref() != authorities_proof.header.hash().as_ref() {
				return Err(ClientError::Backend("Invalid authority warp proof, justification do not match header".to_string()));
		}

		if authorities_proof.header.number() <= previous_checked_block {
			return Err(ClientError::Backend("Invalid authority warp proof".to_string()));
		}
		let current_block = authorities_proof.header.number();
		let mut at_block = None;
		if let Some(sp_finality_grandpa::ScheduledChange {
			next_authorities,
			delay,
		}) = crate::import::find_scheduled_change::<Block>(&authorities_proof.header) {
			let dest = *current_block + delay;
			at_block = Some((dest, next_authorities));
		}
		if let Some((block_number, sp_finality_grandpa::ScheduledChange {
			next_authorities,
			delay,
		})) = crate::import::find_forced_change::<Block>(&authorities_proof.header) {
			let dest = block_number + delay;
			at_block = Some((dest, next_authorities));
		}

		// Fragment without change only allowed for proof last block.
		if at_block.is_none() && !is_last {
			return Err(ClientError::Backend("Invalid authority warp proof".to_string()));
		}
		if let Some((at_block, next_authorities)) = at_block {
			Ok((current_set_id + 1, next_authorities, at_block))
		} else {
			Ok((current_set_id, current_authorities.clone(), current_block.clone()))
		}
}

/// Block info extracted from the justification.
pub(crate) trait BlockJustification<Header: HeaderT> {
	/// Block number justified.
	fn number(&self) -> Header::Number;

	/// Block hash justified.
	fn hash(&self) -> Header::Hash;
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
pub trait ProvableJustification<Header: HeaderT>: Encode + Decode {
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

impl<Block: BlockT> BlockJustification<Block::Header> for GrandpaJustification<Block> {
	fn number(&self) -> NumberFor<Block> {
		self.commit.target_number.clone()
	}
	fn hash(&self) -> Block::Hash {
		self.commit.target_hash.clone()
	}
}

/// Simple cache for warp sync queries.
pub struct WarpSyncFragmentCache<Header: HeaderT> {
	header_has_proof_fragment: std::collections::HashMap<Header::Number, bool>,
	cache: linked_hash_map::LinkedHashMap<
		Header::Number,
		(AuthoritySetProofFragment<Header>, Header::Number),
		>,
	limit: usize,
}

impl<Header: HeaderT> WarpSyncFragmentCache<Header> {
	/// Instantiate a new cache for the warp sync prover.
	pub fn new(size: usize) -> Self {
		WarpSyncFragmentCache {
			header_has_proof_fragment: Default::default(),
			cache: Default::default(),
			limit: size,
		}
	}

	fn new_item(
		&mut self,
		at: Header::Number,
		item: Option<(AuthoritySetProofFragment<Header>, Header::Number)>,
	) {
		self.header_has_proof_fragment.insert(at, item.is_some());

		if let Some(item) = item {
			if self.cache.len() == self.limit {
				self.pop_one();
			}

			self.cache.insert(at, item);
		}
	}

	fn pop_one(&mut self) {
		if let Some((header_number, _)) = self.cache.pop_front() {
			self.header_has_proof_fragment.remove(&header_number);
		}
	}

	fn get_item(
		&mut self,
		block: Header::Number,
	) -> Option<Option<(AuthoritySetProofFragment<Header>, Header::Number)>> {
		match self.header_has_proof_fragment.get(&block) {
			Some(true) => Some(self.cache.get_refresh(&block).cloned()),
			Some(false) => Some(None),
			None => None
		}
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use super::*;
	use crate::authorities::AuthoritySetChanges;
	use sp_core::crypto::Public;
	use sp_finality_grandpa::AuthorityList;
	use sc_client_api::NewBlockState;
	use sc_client_api::in_mem::Blockchain as InMemoryBlockchain;
	use substrate_test_runtime_client::runtime::{Block, Header, H256};

	pub(crate) type FinalityProof = super::FinalityProof<Header>;

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

	#[derive(Debug, PartialEq, Encode, Decode)]
	pub struct TestBlockJustification(TestJustification, u64, H256);

	impl BlockJustification<Header> for TestBlockJustification {
		fn number(&self) -> <Header as HeaderT>::Number {
			self.1
		}
		fn hash(&self) -> <Header as HeaderT>::Hash {
			self.2.clone()
		}
	}

	impl ProvableJustification<Header> for TestBlockJustification {
		fn verify(&self, set_id: u64, authorities: &[(AuthorityId, u64)]) -> ClientResult<()> {
			self.0.verify(set_id, authorities)
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
	fn finality_proof_fails_if_no_more_last_finalized_blocks() {
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
			authority_set_changes,
			*header(3).number(),
		)
		.unwrap();
		assert_eq!(proof_of_3, None);
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
	fn finality_proof_using_authority_set_changes_fails_with_undefined_start() {
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

	#[test]
	fn warp_sync_proof_encoding_decoding() {
		fn test_blockchain(
			nb_blocks: u64,
			mut set_change: &[(u64, Vec<u8>)],
			mut justifications: &[(u64, Vec<u8>)],
		) -> (InMemoryBlockchain<Block>, Vec<H256>) {
			let blockchain = InMemoryBlockchain::<Block>::new();
			let mut hashes = Vec::<H256>::new();
			let mut set_id = 0;
			for i in 0..nb_blocks {
				let mut set_id_next = set_id;
				let mut header = header(i);
				set_change.first()
					.map(|j| if i == j.0 {
						set_change = &set_change[1..];
						let next_authorities: Vec<_> = j.1.iter().map(|i| (AuthorityId::from_slice(&[*i; 32]), 1u64)).collect();
						set_id_next += 1;
						header.digest_mut().logs.push(
							sp_runtime::generic::DigestItem::Consensus(
								sp_finality_grandpa::GRANDPA_ENGINE_ID,
								sp_finality_grandpa::ConsensusLog::ScheduledChange(
									sp_finality_grandpa::ScheduledChange { delay: 0u64, next_authorities }
								).encode(),
							));
					});

				if let Some(parent) = hashes.last() {
					header.set_parent_hash(parent.clone());
				}
				let header_hash = header.hash();

				let justification = justifications.first()
					.and_then(|j| if i == j.0 {
						justifications = &justifications[1..];

						let authority = j.1.iter().map(|j|
							(AuthorityId::from_slice(&[*j; 32]), 1u64)
						).collect();
						let justification = TestBlockJustification(
							TestJustification((set_id, authority), vec![i as u8]),
							i,
							header_hash,
						);
						Some(justification.encode())
					} else {
						None
					});
				hashes.push(header_hash.clone());
				set_id = set_id_next;

				blockchain.insert(header_hash, header, justification, None, NewBlockState::Final)
					.unwrap();
					}
			(blockchain, hashes)
		}

		let (blockchain, hashes) = test_blockchain(
			7,
			vec![(3, vec![9])].as_slice(),
			vec![
			(1, vec![1, 2, 3]),
			(2, vec![1, 2, 3]),
			(3, vec![1, 2, 3]),
			(4, vec![9]),
			(6, vec![9]),
			].as_slice(),
		);

		// proof after set change
		let mut cache = WarpSyncFragmentCache::new(5);
		let proof_no_cache = prove_warp_sync(&blockchain, hashes[6], None, Some(&mut cache)).unwrap();
		let proof = prove_warp_sync(&blockchain, hashes[6], None, Some(&mut cache)).unwrap();
		assert_eq!(proof_no_cache, proof);

		let initial_authorities: Vec<_> = [1u8, 2, 3].iter().map(|i|
			(AuthorityId::from_slice(&[*i; 32]), 1u64)
		).collect();

		let authorities_next: Vec<_> = [9u8].iter().map(|i|
			(AuthorityId::from_slice(&[*i; 32]), 1u64)
		).collect();

		assert!(check_warp_sync_proof::<Block, TestBlockJustification>(
				0,
				initial_authorities.clone(),
				proof.clone(),
		).is_err());
		assert!(check_warp_sync_proof::<Block, TestBlockJustification>(
				0,
				authorities_next.clone(),
				proof.clone(),
		).is_err());
		assert!(check_warp_sync_proof::<Block, TestBlockJustification>(
				1,
				initial_authorities.clone(),
				proof.clone(),
		).is_err());
		let (
			_header,
			current_set_id,
			current_set,
		) = check_warp_sync_proof::<Block, TestBlockJustification>(
		1,
		authorities_next.clone(),
		proof.clone(),
		).unwrap();

		assert_eq!(current_set_id, 1);
		assert_eq!(current_set, authorities_next);

		// proof before set change
		let proof = prove_warp_sync(&blockchain, hashes[1], None, None).unwrap();
		let (
			_header,
			current_set_id,
			current_set,
		) = check_warp_sync_proof::<Block, TestBlockJustification>(
		0,
		initial_authorities.clone(),
		proof.clone(),
		).unwrap();

		assert_eq!(current_set_id, 1);
		assert_eq!(current_set, authorities_next);

		// two changes
		let (blockchain, hashes) = test_blockchain(
			13,
			vec![(3, vec![7]), (8, vec![9])].as_slice(),
			vec![
			(1, vec![1, 2, 3]),
			(2, vec![1, 2, 3]),
			(3, vec![1, 2, 3]),
			(4, vec![7]),
			(6, vec![7]),
			(8, vec![7]), // warning, requires a justification on change set
			(10, vec![9]),
			].as_slice(),
		);

		// proof before set change
		let proof = prove_warp_sync(&blockchain, hashes[1], None, None).unwrap();
		let (
			_header,
			current_set_id,
			current_set,
		) = check_warp_sync_proof::<Block, TestBlockJustification>(
		0,
		initial_authorities.clone(),
		proof.clone(),
		).unwrap();

		assert_eq!(current_set_id, 2);
		assert_eq!(current_set, authorities_next);
	}
}
