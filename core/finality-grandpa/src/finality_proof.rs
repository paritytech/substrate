// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
use log::{trace, warn};

use client::{
	backend::Backend, blockchain::Backend as BlockchainBackend, CallExecutor, Client,
	error::{Error as ClientError, Result as ClientResult},
	light::fetcher::{FetchChecker, RemoteCallRequest},
	ExecutionStrategy, NeverOffchainExt,
};
use parity_codec::{Encode, Decode};
use grandpa::BlockNumberOps;
use runtime_primitives::{Justification, generic::BlockId};
use runtime_primitives::traits::{
	NumberFor, Block as BlockT, Header as HeaderT, One,
};
use substrate_primitives::{H256, Blake2Hasher};
use substrate_telemetry::{telemetry, CONSENSUS_INFO};
use fg_primitives::AuthorityId;

use crate::justification::GrandpaJustification;

/// Maximum number of fragments that we want to return in a single prove_finality call.
const MAX_FRAGMENTS_IN_PROOF: usize = 8;

/// GRANDPA authority set related methods for the finality proof provider.
pub trait AuthoritySetForFinalityProver<Block: BlockT>: Send + Sync {
	/// Call GrandpaApi::grandpa_authorities at given block.
	fn authorities(&self, block: &BlockId<Block>) -> ClientResult<Vec<(AuthorityId, u64)>>;
	/// Prove call of GrandpaApi::grandpa_authorities at given block.
	fn prove_authorities(&self, block: &BlockId<Block>) -> ClientResult<Vec<Vec<u8>>>;
}

/// Client-based implementation of AuthoritySetForFinalityProver.
impl<B, E, Block: BlockT<Hash=H256>, RA> AuthoritySetForFinalityProver<Block> for Client<B, E, Block, RA>
	where
		B: Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
{
	fn authorities(&self, block: &BlockId<Block>) -> ClientResult<Vec<(AuthorityId, u64)>> {
		self.executor().call(
			block,
			"GrandpaApi_grandpa_authorities",
			&[],
			ExecutionStrategy::NativeElseWasm,
			NeverOffchainExt::new(),
		).and_then(|call_result| Decode::decode(&mut &call_result[..])
			.ok_or_else(|| ClientError::CallResultDecode(
				"failed to decode GRANDPA authorities set proof".into(),
			)))
	}

	fn prove_authorities(&self, block: &BlockId<Block>) -> ClientResult<Vec<Vec<u8>>> {
		self.execution_proof(block, "GrandpaApi_grandpa_authorities",&[]).map(|(_, proof)| proof)
	}
}

/// GRANDPA authority set related methods for the finality proof checker.
pub trait AuthoritySetForFinalityChecker<Block: BlockT>: Send + Sync {
	/// Check execution proof of Grandpa::grandpa_authorities at given block.
	fn check_authorities_proof(
		&self,
		hash: Block::Hash,
		header: Block::Header,
		proof: Vec<Vec<u8>>,
	) -> ClientResult<Vec<(AuthorityId, u64)>>;
}

/// FetchChecker-based implementation of AuthoritySetForFinalityChecker.
impl<Block: BlockT> AuthoritySetForFinalityChecker<Block> for Arc<dyn FetchChecker<Block>> {
	fn check_authorities_proof(
		&self,
		hash: Block::Hash,
		header: Block::Header,
		proof: Vec<Vec<u8>>,
	) -> ClientResult<Vec<(AuthorityId, u64)>> {
		let request = RemoteCallRequest {
			block: hash,
			header,
			method: "GrandpaApi_grandpa_authorities".into(),
			call_data: vec![],
			retry_count: None,
		};

		self.check_execution_proof(&request, proof)
			.and_then(|authorities| {
				let authorities: Vec<(AuthorityId, u64)> = Decode::decode(&mut &authorities[..])
					.ok_or_else(|| ClientError::CallResultDecode(
						"failed to decode GRANDPA authorities set proof".into(),
					))?;
				Ok(authorities.into_iter().collect())
			})
	}
}

/// Finality proof provider for serving network requests.
pub struct FinalityProofProvider<B, E, Block: BlockT<Hash=H256>, RA> {
	client: Arc<Client<B, E, Block, RA>>,
	authority_provider: Arc<dyn AuthoritySetForFinalityProver<Block>>,
}

impl<B, E, Block: BlockT<Hash=H256>, RA> FinalityProofProvider<B, E, Block, RA>
	where
		B: Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
{
	/// Create new finality proof provider using:
	///
	/// - client for accessing blockchain data;
	/// - authority_provider for calling and proving runtime methods.
	pub fn new(
		client: Arc<Client<B, E, Block, RA>>,
		authority_provider: Arc<dyn AuthoritySetForFinalityProver<Block>>,
	) -> Self {
		FinalityProofProvider { client, authority_provider }
	}
}

impl<B, E, Block, RA> network::FinalityProofProvider<Block> for FinalityProofProvider<B, E, Block, RA>
	where
		Block: BlockT<Hash=H256>,
		NumberFor<Block>: BlockNumberOps,
		B: Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
{
	fn prove_finality(
		&self,
		for_block: Block::Hash,
		request: &[u8],
	) -> Result<Option<Vec<u8>>, ClientError> {
		let request: FinalityProofRequest<Block::Hash> = Decode::decode(&mut &request[..])
			.ok_or_else(|| {
				warn!(target: "finality", "Unable to decode finality proof request.");
				ClientError::Backend(format!("Invalid finality proof request"))
			})?;
		match request {
			FinalityProofRequest::Original(request) => prove_finality::<_, _, GrandpaJustification<Block>>(
				#[allow(deprecated)]
				&*self.client.backend().blockchain(),
				&*self.authority_provider,
				request.authorities_set_id,
				request.last_finalized,
				for_block,
			),
		}
	}
}

/// The effects of block finality.
#[derive(Debug, PartialEq)]
pub struct FinalityEffects<Header: HeaderT> {
	/// The (ordered) set of headers that could be imported.
	pub headers_to_import: Vec<Header>,
	/// The hash of the block that could be finalized.
	pub block: Header::Hash,
	/// The justification for the block.
	pub justification: Vec<u8>,
	/// New authorities set id that should be applied starting from block.
	pub new_set_id: u64,
	/// New authorities set that should be applied starting from block.
	pub new_authorities: Vec<(AuthorityId, u64)>,
}

/// Single fragment of proof-of-finality.
///
/// Finality for block B is proved by providing:
/// 1) the justification for the descendant block F;
/// 2) headers sub-chain (B; F] if B != F;
/// 3) proof of GRANDPA::authorities() if the set changes at block F.
#[derive(Debug, PartialEq, Encode, Decode)]
struct FinalityProofFragment<Header: HeaderT> {
	/// The hash of block F for which justification is provided.
	pub block: Header::Hash,
	/// Justification of the block F.
	pub justification: Vec<u8>,
	/// The set of headers in the range (U; F] that we believe are unknown to the caller. Ordered.
	pub unknown_headers: Vec<Header>,
	/// Optional proof of execution of GRANDPA::authorities().
	pub authorities_proof: Option<Vec<Vec<u8>>>,
}

/// Proof of finality is the ordered set of finality fragments, where:
/// - last fragment provides justification for the best possible block from the requested range;
/// - all other fragments provide justifications for GRANDPA authorities set changes within requested range.
type FinalityProof<Header> = Vec<FinalityProofFragment<Header>>;

/// Finality proof request data.
#[derive(Debug, Encode, Decode)]
enum FinalityProofRequest<H: Encode + Decode> {
	/// Original version of the request.
	Original(OriginalFinalityProofRequest<H>),
}

/// Original version of finality proof request.
#[derive(Debug, Encode, Decode)]
struct OriginalFinalityProofRequest<H: Encode + Decode> {
	/// The authorities set id we are waiting proof from.
	///
	/// The first justification in the proof must be signed by this authority set.
	pub authorities_set_id: u64,
	/// Hash of the last known finalized block.
	pub last_finalized: H,
}

/// Prepare data blob associated with finality proof request.
pub(crate) fn make_finality_proof_request<H: Encode + Decode>(last_finalized: H, authorities_set_id: u64) -> Vec<u8> {
	FinalityProofRequest::Original(OriginalFinalityProofRequest {
		authorities_set_id,
		last_finalized,
	}).encode()
}

/// Prepare proof-of-finality for the best possible block in the range: (begin; end].
///
/// It is assumed that the caller already have a proof-of-finality for the block 'begin'.
/// It is assumed that the caller already knows all blocks in the range (begin; end].
///
/// Returns None if there are no finalized blocks unknown to the caller.
pub(crate) fn prove_finality<Block: BlockT<Hash=H256>, B: BlockchainBackend<Block>, J>(
	blockchain: &B,
	authorities_provider: &dyn AuthoritySetForFinalityProver<Block>,
	authorities_set_id: u64,
	begin: Block::Hash,
	end: Block::Hash,
) -> ::client::error::Result<Option<Vec<u8>>>
	where
		J: ProvableJustification<Block::Header>,
{
	let begin_id = BlockId::Hash(begin);
	let begin_number = blockchain.expect_block_number_from_id(&begin_id)?;

	// early-return if we sure that there are no blocks finalized AFTER begin block
	let info = blockchain.info();
	if info.finalized_number <= begin_number {
		trace!(
			target: "finality",
			"Requested finality proof for descendant of #{} while we only have finalized #{}. Returning empty proof.",
			begin_number,
			info.finalized_number,
		);

		return Ok(None);
	}

	// check if blocks range is valid. It is the caller responsibility to ensure
	// that it only asks peers that know about whole blocks range
	let end_number = blockchain.expect_block_number_from_id(&BlockId::Hash(end))?;
	if begin_number + One::one() > end_number {
		return Err(ClientError::Backend(
			format!("Cannot generate finality proof for invalid range: {}..{}", begin_number, end_number),
		));
	}

	// early-return if we sure that the block is NOT a part of canonical chain
	let canonical_begin = blockchain.expect_block_hash_from_id(&BlockId::Number(begin_number))?;
	if begin != canonical_begin {
		return Err(ClientError::Backend(
			format!("Cannot generate finality proof for non-canonical block: {}", begin),
		));
	}

	// iterate justifications && try to prove finality
	let mut fragment_index = 0;
	let mut current_authorities = authorities_provider.authorities(&begin_id)?;
	let mut current_number = begin_number + One::one();
	let mut finality_proof = Vec::new();
	let mut unknown_headers = Vec::new();
	let mut latest_proof_fragment = None;
	loop {
		let current_id = BlockId::Number(current_number);

		// check if header is unknown to the caller
		if current_number > end_number {
			let unknown_header = blockchain.expect_header(current_id)?;
			unknown_headers.push(unknown_header);
		}

		if let Some(justification) = blockchain.justification(current_id)? {
			// check if the current block enacts new GRANDPA authorities set
			let parent_id = BlockId::Number(current_number - One::one());
			let new_authorities = authorities_provider.authorities(&parent_id)?;
			let new_authorities_proof = if current_authorities != new_authorities {
				current_authorities = new_authorities;
				Some(authorities_provider.prove_authorities(&parent_id)?)
			} else {
				None
			};

			// prepare finality proof for the current block
			let current = blockchain.expect_block_hash_from_id(&BlockId::Number(current_number))?;
			let proof_fragment = FinalityProofFragment {
				block: current,
				justification,
				unknown_headers: ::std::mem::replace(&mut unknown_headers, Vec::new()),
				authorities_proof: new_authorities_proof,
			};

			// append justification to finality proof if required
			let justifies_end_block = current_number >= end_number;
			let justifies_authority_set_change = proof_fragment.authorities_proof.is_some();
			if justifies_end_block || justifies_authority_set_change {
				// check if the proof is generated by the requested authority set
				if finality_proof.is_empty() {
					let justification_check_result = J::decode_and_verify(
						&proof_fragment.justification,
						authorities_set_id,
						&current_authorities,
					);
					if justification_check_result.is_err() {
						trace!(
							target: "finality",
							"Can not provide finality proof with requested set id #{}\
							(possible forced change?). Returning empty proof.",
							authorities_set_id,
						);

						return Ok(None);
					}
				}

				finality_proof.push(proof_fragment);
				latest_proof_fragment = None;
			} else {
				latest_proof_fragment = Some(proof_fragment);
			}

			// we don't need to provide more justifications
			if justifies_end_block {
				break;
			}
		}

		// we can't provide more justifications
		if current_number == info.finalized_number {
			// append last justification - even if we can't generate finality proof for
			// the end block, we try to generate it for the latest possible block
			if let Some(latest_proof_fragment) = latest_proof_fragment.take() {
				finality_proof.push(latest_proof_fragment);

				fragment_index += 1;
				if fragment_index == MAX_FRAGMENTS_IN_PROOF {
					break;
				}
			}
			break;
		}

		// else search for the next justification
		current_number = current_number + One::one();
	}

	if finality_proof.is_empty() {
		trace!(
			target: "finality",
			"No justifications found when making finality proof for {}. Returning empty proof.",
			end,
		);

		Ok(None)
	} else {
		trace!(
			target: "finality",
			"Built finality proof for {} of {} fragments. Last fragment for {}.",
			end,
			finality_proof.len(),
			finality_proof.last().expect("checked that !finality_proof.is_empty(); qed").block,
		);

		Ok(Some(finality_proof.encode()))
	}
}

/// Check GRANDPA proof-of-finality for the given block.
///
/// Returns the vector of headers that MUST be validated + imported
/// AND if at least one of those headers is invalid, all other MUST be considered invalid.
pub(crate) fn check_finality_proof<Block: BlockT<Hash=H256>, B>(
	blockchain: &B,
	current_set_id: u64,
	current_authorities: Vec<(AuthorityId, u64)>,
	authorities_provider: &dyn AuthoritySetForFinalityChecker<Block>,
	remote_proof: Vec<u8>,
) -> ClientResult<FinalityEffects<Block::Header>>
	where
		NumberFor<Block>: BlockNumberOps,
		B: BlockchainBackend<Block>,
{
	do_check_finality_proof::<_, _, GrandpaJustification<Block>>(
		blockchain,
		current_set_id,
		current_authorities,
		authorities_provider,
		remote_proof)
}

fn do_check_finality_proof<Block: BlockT<Hash=H256>, B, J>(
	blockchain: &B,
	current_set_id: u64,
	current_authorities: Vec<(AuthorityId, u64)>,
	authorities_provider: &dyn AuthoritySetForFinalityChecker<Block>,
	remote_proof: Vec<u8>,
) -> ClientResult<FinalityEffects<Block::Header>>
	where
		NumberFor<Block>: BlockNumberOps,
		B: BlockchainBackend<Block>,
		J: ProvableJustification<Block::Header>,
{
	// decode finality proof
	let proof = FinalityProof::<Block::Header>::decode(&mut &remote_proof[..])
		.ok_or_else(|| ClientError::BadJustification("failed to decode finality proof".into()))?;

	// empty proof can't prove anything
	if proof.is_empty() {
		return Err(ClientError::BadJustification("empty proof of finality".into()));
	}

	// iterate and verify proof fragments
	let last_fragment_index = proof.len() - 1;
	let mut authorities = AuthoritiesOrEffects::Authorities(current_set_id, current_authorities);
	for (proof_fragment_index, proof_fragment) in proof.into_iter().enumerate() {
		// check that proof is non-redundant. The proof still can be valid, but
		// we do not want peer to spam us with redundant data
		if proof_fragment_index != last_fragment_index {
			let has_unknown_headers = !proof_fragment.unknown_headers.is_empty();
			let has_new_authorities = proof_fragment.authorities_proof.is_some();
			if has_unknown_headers || !has_new_authorities {
				return Err(ClientError::BadJustification("redundant proof of finality".into()));
			}
		}

		authorities = check_finality_proof_fragment::<_, _, J>(
			blockchain,
			authorities,
			authorities_provider,
			proof_fragment)?;
	}

	let effects = authorities.extract_effects().expect("at least one loop iteration is guaranteed
			because proof is not empty;\
			check_finality_proof_fragment is called on every iteration;\
			check_finality_proof_fragment always returns FinalityEffects;\
			qed");

	telemetry!(CONSENSUS_INFO; "afg.finality_proof_ok";
		"set_id" => ?effects.new_set_id, "finalized_header_hash" => ?effects.block);

	Ok(effects)
}

/// Check finality proof for the single block.
fn check_finality_proof_fragment<Block: BlockT<Hash=H256>, B, J>(
	blockchain: &B,
	authority_set: AuthoritiesOrEffects<Block::Header>,
	authorities_provider: &dyn AuthoritySetForFinalityChecker<Block>,
	proof_fragment: FinalityProofFragment<Block::Header>,
) -> ClientResult<AuthoritiesOrEffects<Block::Header>>
	where
		NumberFor<Block>: BlockNumberOps,
		B: BlockchainBackend<Block>,
		J: Decode + ProvableJustification<Block::Header>,
{
	// verify justification using previous authorities set
	let (mut current_set_id, mut current_authorities) = authority_set.extract_authorities();
	let justification: J = Decode::decode(&mut &proof_fragment.justification[..])
		.ok_or_else(|| ClientError::JustificationDecode)?;
	justification.verify(current_set_id, &current_authorities)?;

	// and now verify new authorities proof (if provided)
	if let Some(new_authorities_proof) = proof_fragment.authorities_proof {
		// it is safe to query header here, because its non-finality proves that it can't be pruned
		let header = blockchain.expect_header(BlockId::Hash(proof_fragment.block))?;
		let parent_hash = *header.parent_hash();
		let parent_header = blockchain.expect_header(BlockId::Hash(parent_hash))?;
		current_authorities = authorities_provider.check_authorities_proof(
			parent_hash,
			parent_header,
			new_authorities_proof,
		)?;

		current_set_id = current_set_id + 1;
	}

	Ok(AuthoritiesOrEffects::Effects(FinalityEffects {
		headers_to_import: proof_fragment.unknown_headers,
		block: proof_fragment.block,
		justification: proof_fragment.justification,
		new_set_id: current_set_id,
		new_authorities: current_authorities,
	}))
}

/// Authorities set from initial authorities set or finality effects.
enum AuthoritiesOrEffects<Header: HeaderT> {
	Authorities(u64, Vec<(AuthorityId, u64)>),
	Effects(FinalityEffects<Header>),
}

impl<Header: HeaderT> AuthoritiesOrEffects<Header> {
	pub fn extract_authorities(self) -> (u64, Vec<(AuthorityId, u64)>) {
		match self {
			AuthoritiesOrEffects::Authorities(set_id, authorities) => (set_id, authorities),
			AuthoritiesOrEffects::Effects(effects) => (effects.new_set_id, effects.new_authorities),
		}
	}

	pub fn extract_effects(self) -> Option<FinalityEffects<Header>> {
		match self {
			AuthoritiesOrEffects::Authorities(_, _) => None,
			AuthoritiesOrEffects::Effects(effects) => Some(effects),
		}
	}
}

/// Justification used to prove block finality.
pub(crate) trait ProvableJustification<Header: HeaderT>: Encode + Decode {
	/// Verify justification with respect to authorities set and authorities set id.
	fn verify(&self, set_id: u64, authorities: &[(AuthorityId, u64)]) -> ClientResult<()>;

	/// Decode and verify justification.
	fn decode_and_verify(
		justification: &Justification,
		set_id: u64,
		authorities: &[(AuthorityId, u64)],
	) -> ClientResult<Self> {
		let justification = Self::decode(&mut &**justification).ok_or(ClientError::JustificationDecode)?;
		justification.verify(set_id, authorities)?;
		Ok(justification)
	}
}

impl<Block: BlockT<Hash=H256>> ProvableJustification<Block::Header> for GrandpaJustification<Block>
	where
		NumberFor<Block>: BlockNumberOps,
{
	fn verify(&self, set_id: u64, authorities: &[(AuthorityId, u64)]) -> ClientResult<()> {
		GrandpaJustification::verify(self, set_id, &authorities.iter().cloned().collect())
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use test_client::runtime::{Block, Header, H256};
	use test_client::client::{backend::NewBlockState};
	use test_client::client::in_mem::Blockchain as InMemoryBlockchain;
	use super::*;

	type FinalityProof = super::FinalityProof<Header>;

	impl<GetAuthorities, ProveAuthorities> AuthoritySetForFinalityProver<Block> for (GetAuthorities, ProveAuthorities)
		where
			GetAuthorities: Send + Sync + Fn(BlockId<Block>) -> ClientResult<Vec<(AuthorityId, u64)>>,
			ProveAuthorities: Send + Sync + Fn(BlockId<Block>) -> ClientResult<Vec<Vec<u8>>>,
	{
		fn authorities(&self, block: &BlockId<Block>) -> ClientResult<Vec<(AuthorityId, u64)>> {
			self.0(*block)
		}

		fn prove_authorities(&self, block: &BlockId<Block>) -> ClientResult<Vec<Vec<u8>>> {
			self.1(*block)
		}
	}

	struct ClosureAuthoritySetForFinalityChecker<Closure>(pub Closure);

	impl<Closure> AuthoritySetForFinalityChecker<Block> for ClosureAuthoritySetForFinalityChecker<Closure>
		where
			Closure: Send + Sync + Fn(H256, Header, Vec<Vec<u8>>) -> ClientResult<Vec<(AuthorityId, u64)>>,
	{
		fn check_authorities_proof(
			&self,
			hash: H256,
			header: Header,
			proof: Vec<Vec<u8>>,
		) -> ClientResult<Vec<(AuthorityId, u64)>> {
			self.0(hash, header, proof)
		}
	}

	#[derive(Debug, PartialEq, Encode, Decode)]
	pub struct TestJustification(pub bool, pub Vec<u8>);

	impl ProvableJustification<Header> for TestJustification {
		fn verify(&self, _set_id: u64, _authorities: &[(AuthorityId, u64)]) -> ClientResult<()> {
			if self.0 {
				Ok(())
			} else {
				Err(ClientError::BadJustification("test".into()))
			}
		}
	}

	fn header(number: u64) -> Header {
		let parent_hash = match number {
			0 => Default::default(),
			_ => header(number - 1).hash(),
		};
		Header::new(number, H256::from_low_u64_be(0), H256::from_low_u64_be(0), parent_hash, Default::default())
	}

	fn side_header(number: u64) -> Header {
		Header::new(
			number,
			H256::from_low_u64_be(0),
			H256::from_low_u64_be(1),
			header(number - 1).hash(),
			Default::default(),
		)
	}

	fn second_side_header(number: u64) -> Header {
		Header::new(
			number,
			H256::from_low_u64_be(0),
			H256::from_low_u64_be(1),
			side_header(number - 1).hash(),
			Default::default(),
		)
	}

	fn test_blockchain() -> InMemoryBlockchain<Block> {
		let blockchain = InMemoryBlockchain::<Block>::new();
		blockchain.insert(header(0).hash(), header(0), Some(vec![0]), None, NewBlockState::Final).unwrap();
		blockchain.insert(header(1).hash(), header(1), Some(vec![1]), None, NewBlockState::Final).unwrap();
		blockchain.insert(header(2).hash(), header(2), None, None, NewBlockState::Best).unwrap();
		blockchain.insert(header(3).hash(), header(3), Some(vec![3]), None, NewBlockState::Final).unwrap();
		blockchain
	}

	#[test]
	fn finality_prove_fails_with_invalid_range() {
		let blockchain = test_blockchain();

		// their last finalized is: 2
		// they request for proof-of-finality of: 2
		// => range is invalid
		prove_finality::<_, _, TestJustification>(
			&blockchain,
			&(
				|_| unreachable!("should return before calling GetAuthorities"),
				|_| unreachable!("should return before calling ProveAuthorities"),
			),
			0,
			header(2).hash(),
			header(2).hash(),
		).unwrap_err();
	}

	#[test]
	fn finality_proof_is_none_if_no_more_last_finalized_blocks() {
		let blockchain = test_blockchain();
		blockchain.insert(header(4).hash(), header(4), None, None, NewBlockState::Best).unwrap();

		// our last finalized is: 3
		// their last finalized is: 3
		// => we can't provide any additional justifications
		let proof_of_4 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&(
				|_| unreachable!("should return before calling GetAuthorities"),
				|_| unreachable!("should return before calling ProveAuthorities"),
			),
			0,
			header(3).hash(),
			header(4).hash(),
		).unwrap();
		assert_eq!(proof_of_4, None);
	}

	#[test]
	fn finality_proof_fails_for_non_canonical_block() {
		let blockchain = test_blockchain();
		blockchain.insert(header(4).hash(), header(4), None, None, NewBlockState::Best).unwrap();
		blockchain.insert(side_header(4).hash(), side_header(4), None, None, NewBlockState::Best).unwrap();
		blockchain.insert(second_side_header(5).hash(), second_side_header(5), None, None, NewBlockState::Best)
			.unwrap();
		blockchain.insert(header(5).hash(), header(5), Some(vec![5]), None, NewBlockState::Final).unwrap();

		// chain is 1 -> 2 -> 3 -> 4 -> 5
		//                      \> 4' -> 5'
		// and the best finalized is 5
		// => when requesting for (4'; 5'], error is returned
		prove_finality::<_, _, TestJustification>(
			&blockchain,
			&(
				|_| unreachable!("should return before calling GetAuthorities"),
				|_| unreachable!("should return before calling ProveAuthorities"),
			),
			0,
			side_header(4).hash(),
			second_side_header(5).hash(),
		).unwrap_err();
	}

	#[test]
	fn finality_proof_is_none_if_no_justification_known() {
		let blockchain = test_blockchain();
		blockchain.insert(header(4).hash(), header(4), None, None, NewBlockState::Final).unwrap();

		// block 4 is finalized without justification
		// => we can't prove finality
		let proof_of_4 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&(
				|_| Ok(vec![(AuthorityId::from_raw([1u8; 32]), 1u64)]),
				|_| unreachable!("authorities didn't change => ProveAuthorities won't be called"),
			),
			0,
			header(3).hash(),
			header(4).hash(),
		).unwrap();
		assert_eq!(proof_of_4, None);
	}

	#[test]
	fn finality_proof_works_without_authorities_change() {
		let blockchain = test_blockchain();
		let just4 = TestJustification(true, vec![4]).encode();
		let just5 = TestJustification(true, vec![5]).encode();
		blockchain.insert(header(4).hash(), header(4), Some(just4), None, NewBlockState::Final).unwrap();
		blockchain.insert(header(5).hash(), header(5), Some(just5.clone()), None, NewBlockState::Final).unwrap();

		// blocks 4 && 5 are finalized with justification
		// => since authorities are the same, we only need justification for 5
		let proof_of_5: FinalityProof = Decode::decode(&mut &prove_finality::<_, _, TestJustification>(
			&blockchain,
			&(
				|_| Ok(vec![(AuthorityId::from_raw([1u8; 32]), 1u64)]),
				|_| unreachable!("should return before calling ProveAuthorities"),
			),
			0,
			header(3).hash(),
			header(5).hash(),
		).unwrap().unwrap()[..]).unwrap();
		assert_eq!(proof_of_5, vec![FinalityProofFragment {
			block: header(5).hash(),
			justification: just5,
			unknown_headers: Vec::new(),
			authorities_proof: None,
		}]);
	}

	#[test]
	fn finality_proof_finalized_earlier_block_if_no_justification_for_target_is_known() {
		let blockchain = test_blockchain();
		blockchain.insert(header(4).hash(), header(4), Some(vec![4]), None, NewBlockState::Final).unwrap();
		blockchain.insert(header(5).hash(), header(5), None, None, NewBlockState::Final).unwrap();

		// block 4 is finalized with justification + we request for finality of 5
		// => we can't prove finality of 5, but providing finality for 4 is still useful for requester
		let proof_of_5: FinalityProof = Decode::decode(&mut &prove_finality::<_, _, TestJustification>(
			&blockchain,
			&(
				|_| Ok(vec![(AuthorityId::from_raw([1u8; 32]), 1u64)]),
				|_| unreachable!("should return before calling ProveAuthorities"),
			),
			0,
			header(3).hash(),
			header(5).hash(),
		).unwrap().unwrap()[..]).unwrap();
		assert_eq!(proof_of_5, vec![FinalityProofFragment {
			block: header(4).hash(),
			justification: vec![4],
			unknown_headers: Vec::new(),
			authorities_proof: None,
		}]);
	}

	#[test]
	fn finality_proof_works_with_authorities_change() {
		let blockchain = test_blockchain();
		let just4 = TestJustification(true, vec![4]).encode();
		let just5 = TestJustification(true, vec![5]).encode();
		let just7 = TestJustification(true, vec![7]).encode();
		blockchain.insert(header(4).hash(), header(4), Some(just4), None, NewBlockState::Final).unwrap();
		blockchain.insert(header(5).hash(), header(5), Some(just5.clone()), None, NewBlockState::Final).unwrap();
		blockchain.insert(header(6).hash(), header(6), None, None, NewBlockState::Final).unwrap();
		blockchain.insert(header(7).hash(), header(7), Some(just7.clone()), None, NewBlockState::Final).unwrap();

		// when querying for finality of 6, we assume that the #6 is the last block known to the requester
		// => since we only have justification for #7, we provide #7
		let proof_of_6: FinalityProof = Decode::decode(&mut &prove_finality::<_, _, TestJustification>(
			&blockchain,
			&(
				|block_id| match block_id {
					BlockId::Hash(h) if h == header(3).hash() => Ok(vec![(AuthorityId::from_raw([3u8; 32]), 1u64)]),
					BlockId::Number(3) => Ok(vec![(AuthorityId::from_raw([3u8; 32]), 1u64)]),
					BlockId::Number(4) => Ok(vec![(AuthorityId::from_raw([4u8; 32]), 1u64)]),
					BlockId::Number(6) => Ok(vec![(AuthorityId::from_raw([6u8; 32]), 1u64)]),
					_ => unreachable!("no other authorities should be fetched: {:?}", block_id),
				},
				|block_id| match block_id {
					BlockId::Number(4) => Ok(vec![vec![40]]),
					BlockId::Number(6) => Ok(vec![vec![60]]),
					_ => unreachable!("no other authorities should be proved: {:?}", block_id),
				},
			),
			0,
			header(3).hash(),
			header(6).hash(),
		).unwrap().unwrap()[..]).unwrap();
		// initial authorities set (which start acting from #4) is [3; 32]
		assert_eq!(proof_of_6, vec![
			// new authorities set starts acting from #5 => we do not provide fragment for #4
			// first fragment provides justification for #5 && authorities set that starts acting from #5
			FinalityProofFragment {
				block: header(5).hash(),
				justification: just5,
				unknown_headers: Vec::new(),
				authorities_proof: Some(vec![vec![40]]),
			},
			// last fragment provides justification for #7 && unknown#7
			FinalityProofFragment {
				block: header(7).hash(),
				justification: just7,
				unknown_headers: vec![header(7)],
				authorities_proof: Some(vec![vec![60]]),
			},
		]);
	}

	#[test]
	fn finality_proof_check_fails_when_proof_decode_fails() {
		let blockchain = test_blockchain();

		// when we can't decode proof from Vec<u8>
		do_check_finality_proof::<_, _, TestJustification>(
			&blockchain,
			1,
			vec![(AuthorityId::from_raw([3u8; 32]), 1u64)],
			&ClosureAuthoritySetForFinalityChecker(|_, _, _| unreachable!("returns before CheckAuthoritiesProof")),
			vec![42],
		).unwrap_err();
	}

	#[test]
	fn finality_proof_check_fails_when_proof_is_empty() {
		let blockchain = test_blockchain();

		// when decoded proof has zero length
		do_check_finality_proof::<_, _, TestJustification>(
			&blockchain,
			1,
			vec![(AuthorityId::from_raw([3u8; 32]), 1u64)],
			&ClosureAuthoritySetForFinalityChecker(|_, _, _| unreachable!("returns before CheckAuthoritiesProof")),
			Vec::<TestJustification>::new().encode(),
		).unwrap_err();
	}

	#[test]
	fn finality_proof_check_fails_when_intemediate_fragment_has_unknown_headers() {
		let blockchain = test_blockchain();

		// when intermediate (#0) fragment has non-empty unknown headers
		do_check_finality_proof::<_, _, TestJustification>(
			&blockchain,
			1,
			vec![(AuthorityId::from_raw([3u8; 32]), 1u64)],
			&ClosureAuthoritySetForFinalityChecker(|_, _, _| unreachable!("returns before CheckAuthoritiesProof")),
			vec![FinalityProofFragment {
				block: header(4).hash(),
				justification: TestJustification(true, vec![7]).encode(),
				unknown_headers: vec![header(4)],
				authorities_proof: Some(vec![vec![42]]),
			}, FinalityProofFragment {
				block: header(5).hash(),
				justification: TestJustification(true, vec![8]).encode(),
				unknown_headers: vec![header(5)],
				authorities_proof: None,
			}].encode(),
		).unwrap_err();
	}

	#[test]
	fn finality_proof_check_fails_when_intemediate_fragment_has_no_authorities_proof() {
		let blockchain = test_blockchain();

		// when intermediate (#0) fragment has empty authorities proof
		do_check_finality_proof::<_, _, TestJustification>(
			&blockchain,
			1,
			vec![(AuthorityId::from_raw([3u8; 32]), 1u64)],
			&ClosureAuthoritySetForFinalityChecker(|_, _, _| unreachable!("returns before CheckAuthoritiesProof")),
			vec![FinalityProofFragment {
				block: header(4).hash(),
				justification: TestJustification(true, vec![7]).encode(),
				unknown_headers: Vec::new(),
				authorities_proof: None,
			}, FinalityProofFragment {
				block: header(5).hash(),
				justification: TestJustification(true, vec![8]).encode(),
				unknown_headers: vec![header(5)],
				authorities_proof: None,
			}].encode(),
		).unwrap_err();
	}

	#[test]
	fn finality_proof_check_works() {
		let blockchain = test_blockchain();

		let effects = do_check_finality_proof::<_, _, TestJustification>(
			&blockchain,
			1,
			vec![(AuthorityId::from_raw([3u8; 32]), 1u64)],
			&ClosureAuthoritySetForFinalityChecker(|_, _, _| Ok(vec![(AuthorityId::from_raw([4u8; 32]), 1u64)])),
			vec![FinalityProofFragment {
				block: header(2).hash(),
				justification: TestJustification(true, vec![7]).encode(),
				unknown_headers: Vec::new(),
				authorities_proof: Some(vec![vec![42]]),
			}, FinalityProofFragment {
				block: header(4).hash(),
				justification: TestJustification(true, vec![8]).encode(),
				unknown_headers: vec![header(4)],
				authorities_proof: None,
			}].encode(),
		).unwrap();
		assert_eq!(effects, FinalityEffects {
			headers_to_import: vec![header(4)],
			block: header(4).hash(),
			justification: TestJustification(true, vec![8]).encode(),
			new_set_id: 2,
			new_authorities: vec![(AuthorityId::from_raw([4u8; 32]), 1u64)],
		});
	}

	#[test]
	fn finality_proof_is_none_if_first_justification_is_generated_by_unknown_set() {
		// this is the case for forced change: set_id has been forcibly increased on full node
		// and ligh node missed that
		// => justification verification will fail on light node anyways, so we do not return
		// finality proof at all
		let blockchain = test_blockchain();
		let just4 = TestJustification(false, vec![4]).encode(); // false makes verification fail
		blockchain.insert(header(4).hash(), header(4), Some(just4), None, NewBlockState::Final).unwrap();

		let proof_of_4 = prove_finality::<_, _, TestJustification>(
			&blockchain,
			&(
				|_| Ok(vec![(AuthorityId::from_raw([1u8; 32]), 1u64)]),
				|_| unreachable!("should return before calling ProveAuthorities"),
			),
			0,
			header(3).hash(),
			header(4).hash(),
		).unwrap();
		assert!(proof_of_4.is_none());
	}
}
