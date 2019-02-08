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

//! GRANDPA block finality proof generation and check.
//!
//! Finality of block B is proved by providing:
//! 1) valid headers sub-chain from the block B to the block F;
//! 2) valid (with respect to proved authorities) GRANDPA justification of the block F;
//! 3) proof-of-execution of the `grandpa_authorities` call at the block F.
//!
//! Since earliest possible justification is returned, the GRANDPA authorities set
//! at the block F is guaranteed to be the same as in the block B (this is because block
//! that enacts new GRANDPA authorities set always comes with justification). It also
//! means that the `set_id` is the same at blocks B and F.
//!
//! The caller should track the `set_id`. The most straightforward way is to fetch finality
//! proofs ONLY for blocks on the tip of the chain and track the latest known `set_id`.

use grandpa::VoterSet;

use client::{
	blockchain::Backend as BlockchainBackend,
	error::{ErrorKind as ClientErrorKind, Result as ClientResult},
};
use codec::{Encode, Decode};
use grandpa::BlockNumberOps;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{
	NumberFor, Block as BlockT, Header as HeaderT, One,
};
use substrate_primitives::{Ed25519AuthorityId, H256};

use GrandpaJustification;

/// The effects of block finality.
pub struct FinalityEffects<Header: HeaderT, J> {
	/// The (ordered) set of headers that could be imported.
	pub headers_to_import: Vec<Header>,
	/// The hash of the block that could be finalized.
	pub block: Header::Hash,
	/// The justification for the block.
	pub justification: J,
	/// New authorities set id that should be applied starting from block.
	pub new_set_id: u64,
	/// New authorities set that should be applied starting from block.
	pub new_authorities: VoterSet<Ed25519AuthorityId>,
}

/// Single fragment of proof-of-finality.
///
/// Finality for block B is proved by providing:
/// 1) the justification for the descendant block F;
/// 2) headers sub-chain (U; F], where U is the last block known to the caller;
/// 3) proof of GRANDPA::authorities() if the set changes at block F.
#[derive(Debug, PartialEq, Encode, Decode)]
struct FinalityProofFragment<Header: HeaderT, Justification> {
	/// The hash of block F for which justification is provided.
	pub block: Header::Hash,
	/// Justification of the block F.
	pub justification: Justification,
	/// The set of headers in the range (U; F] that we believe are unknown to the caller. Ordered.
	pub unknown_headers: Vec<Header>,
	/// Optional proof of execution of GRANDPA::authorities().
	pub authorities_proof: Option<Vec<Vec<u8>>>,
}

/// Proof of finality is the ordered set of finality fragments, where:
/// - last fragment provides justification for the best possible block from the requested range;
/// - all other fragments provide justifications for GRANDPA authorities set changes within requested range.
type FinalityProof<Header: HeaderT, Justification> = Vec<FinalityProofFragment<Header, Justification>>;

/// Prepare proof-of-finality for the best possible block in the range: (begin; end].
///
/// It is assumed that the caller already have a proof-of-finality for the block 'begin'.
/// It is assumed that the caller already knows all blocks in the range (begin; end].
///
/// Returns None if there are no finalized blocks unknown to the caller.
pub fn prove_finality<Block: BlockT<Hash=H256>, B, GetAuthorities, ProveAuthorities>(
	blockchain: &B,
	get_authorities: GetAuthorities,
	prove_authorities: ProveAuthorities,
	begin: Block::Hash,
	end: Block::Hash,
) -> ::client::error::Result<Option<Vec<u8>>>
	where
		B: BlockchainBackend<Block>,
		GetAuthorities: Fn(&BlockId<Block>) -> ClientResult<Vec<u8>>,
		ProveAuthorities: Fn(&BlockId<Block>) -> ClientResult<Vec<Vec<u8>>>,
{
	let begin_id = BlockId::Hash(begin);
	let begin_number = blockchain.expect_block_number_from_id(&begin_id)?;

	// early-return if we sure that there are no blocks finalized AFTER begin block
	let info = blockchain.info()?;
	if info.finalized_number <= begin_number {
		return Ok(None);
	}

	// check if blocks range is valid. It is the caller responsibility to ensure
	// that it only asks peers that know about whole blocks range
	let end_number = blockchain.expect_block_number_from_id(&BlockId::Hash(end))?;
	if begin_number + One::one() > end_number {
		return Err(ClientErrorKind::Backend(
			format!("Cannot generate finality proof for invalid range: {}..{}", begin_number, end_number),
		).into());
	}

	// early-return if we sure that the block is NOT a part of canonical chain
	let canonical_begin = blockchain.expect_block_hash_from_id(&BlockId::Number(begin_number))?;
	if begin != canonical_begin {
		return Err(ClientErrorKind::Backend(
			format!("Cannot generate finality proof for non-canonical block: {}", begin),
		).into());
	}

	// iterate justifications && try to prove finality
	let mut current_authorities = get_authorities(&begin_id)?;
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
			let new_authorities = get_authorities(&parent_id)?;
			let new_authorities_proof = if current_authorities != new_authorities {
				current_authorities = new_authorities;
				Some(prove_authorities(&parent_id)?)
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
			}
			break;
		}

		// else search for the next justification
		current_number = current_number + One::one();
	}

	if finality_proof.is_empty() {
		Ok(None)
	} else {
		Ok(Some(finality_proof.encode()))
	}
}

/// Check proof-of-finality for the given block.
///
/// Returns the vector of headers that MUST be validated + imported
/// AND. If at least one of those headers
/// is invalid, all other MUST be considered invalid.
pub(crate) fn check_finality_proof<Block: BlockT<Hash=H256>, B, CheckAuthoritiesProof>(
	blockchain: &B,
	current_set_id: u64,
	current_authorities: VoterSet<Ed25519AuthorityId>,
	check_authorities_proof: CheckAuthoritiesProof,
	remote_proof: Vec<u8>,
) -> ClientResult<FinalityEffects<Block::Header, GrandpaJustification<Block>>>
	where
		NumberFor<Block>: BlockNumberOps,
		B: BlockchainBackend<Block>,
		CheckAuthoritiesProof: Fn(
			Block::Hash,
			Block::Header,
			Vec<Vec<u8>>,
		) -> ClientResult<VoterSet<Ed25519AuthorityId>>,
{
	do_check_finality_proof(
		blockchain,
		current_set_id,
		current_authorities,
		check_authorities_proof,
		remote_proof)
}

/// Check proof-of-finality for the given block.
///
/// Returns the vector of headers that MUST be validated + imported
/// AND. If at least one of those headers
/// is invalid, all other MUST be considered invalid.
fn do_check_finality_proof<Block: BlockT<Hash=H256>, B, J, CheckAuthoritiesProof>(
	blockchain: &B,
	current_set_id: u64,
	current_authorities: VoterSet<Ed25519AuthorityId>,
	check_authorities_proof: CheckAuthoritiesProof,
	remote_proof: Vec<u8>,
) -> ClientResult<FinalityEffects<Block::Header, J>>
	where
		NumberFor<Block>: BlockNumberOps,
		B: BlockchainBackend<Block>,
		J: ProvableJustification<Block::Header>,
		CheckAuthoritiesProof: Fn(
			Block::Hash,
			Block::Header,
			Vec<Vec<u8>>,
		) -> ClientResult<VoterSet<Ed25519AuthorityId>>,
{
	// decode finality proof
	let proof = FinalityProof::<Block::Header, J>::decode(&mut &remote_proof[..])
		.ok_or_else(|| ClientErrorKind::BadJustification("failed to decode finality proof".into()))?;

	// empty proof can't prove anything
	if proof.is_empty() {
		return Err(ClientErrorKind::BadJustification("empty proof of finality".into()).into());
	}

	// iterate and verify proof fragments
	let last_fragment_index = proof.len() - 1;
	let mut authorities = AuthoritiesOrEffects::Authorities(current_set_id, current_authorities);
	for (proof_fragment_index, proof_fragment) in proof.into_iter().enumerate() {
		// check that proof is non-redundant. The proof still can be valid, but
		// we do not want peer to spam us with redundant data
		if proof_fragment_index == last_fragment_index {
			let has_unknown_headers = proof_fragment.unknown_headers.is_empty();
			let has_new_authorities = proof_fragment.authorities_proof.is_some();
			if has_unknown_headers || !has_new_authorities {
				return Err(ClientErrorKind::BadJustification("redundant proof of finality".into()).into());
			}
		}

		authorities = check_finality_proof_fragment(
			blockchain,
			authorities,
			&check_authorities_proof,
			proof_fragment)?;
	}

	Ok(authorities.extract_effects().expect("at least one loop iteration is guaranteed because proof is not empty;\
		check_finality_proof_fragment is called on every iteration;\
		check_finality_proof_fragment always returns FinalityEffects;\
		qed"))
}

/// Check finality proof for the single block.
fn check_finality_proof_fragment<Block: BlockT<Hash=H256>, B, J, CheckAuthoritiesProof>(
	blockchain: &B,
	authority_set: AuthoritiesOrEffects<Block::Header, J>,
	check_authorities_proof: &CheckAuthoritiesProof,
	proof_fragment: FinalityProofFragment<Block::Header, J>,
) -> ClientResult<AuthoritiesOrEffects<Block::Header, J>>
	where
		NumberFor<Block>: BlockNumberOps,
		B: BlockchainBackend<Block>,
		J: ProvableJustification<Block::Header>,
		CheckAuthoritiesProof: Fn(
			Block::Hash,
			Block::Header,
			Vec<Vec<u8>>,
		) -> ClientResult<VoterSet<Ed25519AuthorityId>>,
{
	// verify justification using previous authorities set
	let (mut current_set_id, mut current_authorities) = authority_set.extract_authorities();
	proof_fragment.justification.verify(current_set_id, &current_authorities)?;

	// and now verify new authorities proof (if provided)
	if let Some(new_authorities_proof) = proof_fragment.authorities_proof {
		// it is safe to query header here, because its non-finality proves that it can't be pruned
		let header = blockchain.expect_header(BlockId::Hash(proof_fragment.block))?;
		current_authorities = check_authorities_proof(proof_fragment.block, header, new_authorities_proof)?;
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
enum AuthoritiesOrEffects<Header: HeaderT, J> {
	Authorities(u64, VoterSet<Ed25519AuthorityId>),
	Effects(FinalityEffects<Header, J>),
}

impl<Header: HeaderT, J> AuthoritiesOrEffects<Header, J> {
	pub fn extract_authorities(self) -> (u64, VoterSet<Ed25519AuthorityId>) {
		match self {
			AuthoritiesOrEffects::Authorities(set_id, authorities) => (set_id, authorities),
			AuthoritiesOrEffects::Effects(effects) => (effects.new_set_id, effects.new_authorities),
		}
	}

	pub fn extract_effects(self) -> Option<FinalityEffects<Header, J>> {
		match self {
			AuthoritiesOrEffects::Authorities(_, _) => None,
			AuthoritiesOrEffects::Effects(effects) => Some(effects),
		}
	}
}

/// Justification used to prove block finality.
trait ProvableJustification<Header: HeaderT>: Encode + Decode {
	/// Get target block of this justification.
	fn target_block(&self) -> (Header::Number, Header::Hash);

	/// Verify justification with respect to authorities set and authorities set id.
	fn verify(&self, set_id: u64, authorities: &VoterSet<Ed25519AuthorityId>) -> ClientResult<()>;
}

impl<Block: BlockT<Hash=H256>> ProvableJustification<Block::Header> for GrandpaJustification<Block>
	where
		NumberFor<Block>: BlockNumberOps,
{
	fn target_block(&self) -> (NumberFor<Block>, Block::Hash) {
		(self.commit.target_number, self.commit.target_hash)
	}

	fn verify(&self, set_id: u64, authorities: &VoterSet<Ed25519AuthorityId>) -> ClientResult<()> {
		GrandpaJustification::verify(self, set_id, authorities)
	}
}

/*#[cfg(test)]
mod tests {
	use test_client::runtime::{Block, Header};
	use test_client::client::backend::NewBlockState;
	use test_client::client::in_mem::Blockchain as InMemoryBlockchain;
	use super::*;

	type FinalityProof = super::FinalityProof<Header, Vec<u8>>;

	#[derive(Encode, Decode)]
	struct ValidFinalityProof(Vec<u8>);

	impl ProvableJustification<Header> for ValidFinalityProof {
		fn target_block(&self) -> (u64, H256) { (3, header(3).hash()) }

		fn verify(&self, set_id: u64, authorities: &VoterSet<Ed25519AuthorityId>) -> ClientResult<()> {
			assert_eq!(set_id, 1);
			assert_eq!(authorities, &vec![
				(Ed25519AuthorityId([1u8; 32]), 1),
				(Ed25519AuthorityId([2u8; 32]), 2),
				(Ed25519AuthorityId([3u8; 32]), 3),
			].into_iter().collect());
			Ok(())
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
		Header::new(number, H256::from_low_u64_be(0), H256::from_low_u64_be(1), header(number - 1).hash(), Default::default())
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
	fn finality_proof_is_not_generated_for_non_final_block() {
		let blockchain = test_blockchain();
		blockchain.insert(header(4).hash(), header(4), None, None, NewBlockState::Best).unwrap();

		// when asking for finality of block 4, None is returned
		let proof_of_4 = prove_finality(&blockchain, |_, _, _| Ok(vec![vec![42]]), header(4).hash())
			.unwrap();
		assert_eq!(proof_of_4, None);
	}

	#[test]
	fn finality_proof_fails_for_non_canonical_block() {
		let blockchain = test_blockchain();
		blockchain.insert(header(4).hash(), header(4), None, None, NewBlockState::Best).unwrap();
		blockchain.insert(side_header(4).hash(), side_header(4), None, None, NewBlockState::Best).unwrap();
		blockchain.insert(header(5).hash(), header(5), Some(vec![5]), None, NewBlockState::Final).unwrap();

		// when asking for finality of side-block 42, None is returned
		let proof_of_side_4_fails = prove_finality(&blockchain, |_, _, _| Ok(vec![vec![42]]), H256::from_low_u64_be(42)).is_err();
		assert_eq!(proof_of_side_4_fails, true);
	}

	#[test]
	fn finality_proof_fails_if_no_justification_known() {
		let blockchain = test_blockchain();
		blockchain.insert(header(4).hash(), header(4), None, None, NewBlockState::Final).unwrap();

		// when asking for finality of block 4, search for justification failing
		let proof_of_4_fails = prove_finality(&blockchain, |_, _, _| Ok(vec![vec![42]]), H256::from_low_u64_be(42)).is_err();
		assert_eq!(proof_of_4_fails, true);
	}

	#[test]
	fn prove_finality_is_generated() {
		let blockchain = test_blockchain();

		// when asking for finality of block 2, justification of 3 is returned
		let proof_of_2: FinalityProof = prove_finality(&blockchain, |_, _, _| Ok(vec![vec![42]]), header(2).hash())
			.unwrap().and_then(|p| Decode::decode(&mut &p[..])).unwrap();
		assert_eq!(proof_of_2, FinalityProof {
			finalization_path: vec![header(2), header(3)],
			justification: vec![3],
			authorities_proof: vec![vec![42]],
		});

		// when asking for finality of block 3, justification of 3 is returned
		let proof_of_3: FinalityProof = prove_finality(&blockchain, |_, _, _| Ok(vec![vec![42]]), header(3).hash())
			.unwrap().and_then(|p| Decode::decode(&mut &p[..])).unwrap();
		assert_eq!(proof_of_3, FinalityProof {
			finalization_path: vec![header(3)],
			justification: vec![3],
			authorities_proof: vec![vec![42]],
		});
	}

	#[test]
	fn finality_proof_check_fails_when_block_is_not_included() {
		let mut proof_of_2: FinalityProof = prove_finality(
			&test_blockchain(),
			|_, _, _| Ok(vec![vec![42]]),
			header(2).hash(),
		).unwrap().and_then(|p| Decode::decode(&mut &p[..])).unwrap();
		proof_of_2.finalization_path.remove(0);

		// block for which we're trying to request finality proof is missing from finalization_path
		assert_eq!(do_check_finality_proof::<Block, _, ValidFinalityProof>(
			|_| Ok(Vec::<u8>::new().encode()),
			header(1),
			(2, header(2).hash()),
			1,
			proof_of_2.encode(),
		).is_err(), true);
	}

	#[test]
	fn finality_proof_check_fails_when_justified_block_is_not_included() {
		let mut proof_of_2: FinalityProof = prove_finality(
			&test_blockchain(),
			|_, _, _| Ok(vec![vec![42]]),
			header(2).hash(),
		).unwrap().and_then(|p| Decode::decode(&mut &p[..])).unwrap();
		proof_of_2.finalization_path.remove(1);

		// justified block is missing from finalization_path
		assert_eq!(do_check_finality_proof::<Block, _, ValidFinalityProof>(
			|_| Ok(Vec::<u8>::new().encode()),
			header(1),
			(2, header(2).hash()),
			1,
			proof_of_2.encode(),
		).is_err(), true);
	}

	#[test]
	fn finality_proof_check_fails_when_justification_verification_fails() {
		#[derive(Encode, Decode)]
		struct InvalidFinalityProof(Vec<u8>);

		impl ProvableJustification<Header> for InvalidFinalityProof {
			fn target_block(&self) -> (u64, H256) { (3, header(3).hash()) }

			fn verify(&self, _set_id: u64, _authorities: &VoterSet<Ed25519AuthorityId>) -> ClientResult<()> {
				Err(ClientErrorKind::Backend("test error".into()).into())
			}
		}

		let mut proof_of_2: FinalityProof = prove_finality(
			&test_blockchain(),
			|_, _, _| Ok(vec![vec![42]]),
			header(2).hash(),
		).unwrap().and_then(|p| Decode::decode(&mut &p[..])).unwrap();
		proof_of_2.finalization_path.remove(1);

		// justification is not valid
		assert_eq!(do_check_finality_proof::<Block, _, InvalidFinalityProof>(
			|_| Ok(Vec::<u8>::new().encode()),
			header(1),
			(2, header(2).hash()),
			1,
			proof_of_2.encode(),
		).is_err(), true);
	}

	#[test]
	fn finality_proof_check_works() {
		let proof_of_2 = prove_finality(&test_blockchain(), |_, _, _| Ok(vec![vec![42]]), header(2).hash())
			.unwrap().unwrap();
		assert_eq!(do_check_finality_proof::<Block, _, ValidFinalityProof>(
			|_| Ok(vec![
				(Ed25519AuthorityId([1u8; 32]), 1u64),
				(Ed25519AuthorityId([2u8; 32]), 2u64),
				(Ed25519AuthorityId([3u8; 32]), 3u64),
			].encode()),
			header(1),
			(2, header(2).hash()),
			1,
			proof_of_2,
		).unwrap(), vec![header(2), header(3)]);
	}
}
*/