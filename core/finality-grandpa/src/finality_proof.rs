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

use grandpa::voter_set::VoterSet;

use client::{
	blockchain::Backend as BlockchainBackend,
	error::{Error as ClientError, Result as ClientResult},
	light::fetcher::RemoteCallRequest,
};
use parity_codec::{Encode, Decode};
use grandpa::BlockNumberOps;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{
	NumberFor, Block as BlockT, Header as HeaderT, One,
};
use substrate_primitives::{ed25519, H256};
use ed25519::Public as AuthorityId;
use substrate_telemetry::{telemetry, CONSENSUS_INFO};

use crate::justification::GrandpaJustification;

/// Prepare proof-of-finality for the given block.
///
/// The proof is the serialized `FinalityProof` constructed using earliest known
/// justification of the block. None is returned if there's no known justification atm.
pub fn prove_finality<Block: BlockT, B, G>(
	blockchain: &B,
	generate_execution_proof: G,
	block: Block::Hash,
) -> ::client::error::Result<Option<Vec<u8>>>
	where
		B: BlockchainBackend<Block>,
		G: Fn(&BlockId<Block>, &str, &[u8]) -> ClientResult<Vec<Vec<u8>>>,
{
	let block_id = BlockId::Hash(block);
	let mut block_number = blockchain.expect_block_number_from_id(&block_id)?;

	// early-return if we sure that the block isn't finalized yet
	let info = blockchain.info()?;
	if info.finalized_number < block_number {
		return Ok(None);
	}

	// early-return if we sure that the block is NOT a part of canonical chain
	let canonical_block = blockchain.expect_block_hash_from_id(&BlockId::Number(block_number))?;
	if block != canonical_block {
		return Err(ClientError::Backend(
			"Cannot generate finality proof for non-canonical block".into()
		).into());
	}

	// now that we know that the block is finalized, we can generate finalization proof

	// we need to prove grandpa authorities set that has generated justification
	// BUT since `GrandpaApi::grandpa_authorities` call returns the set that becames actual
	// at the next block, the proof-of execution is generated using parent block' state
	// (this will fail if we're trying to prove genesis finality, but such the call itself is redundant)
	let mut current_header = blockchain.expect_header(BlockId::Hash(block))?;
	let parent_block_id = BlockId::Hash(*current_header.parent_hash());
	let authorities_proof = generate_execution_proof(
		&parent_block_id,
		"GrandpaApi_grandpa_authorities",
		&[],
	)?;

	// search for earliest post-block (inclusive) justification
	let mut finalization_path = Vec::new();
	loop {
		finalization_path.push(current_header);

		match blockchain.justification(BlockId::Number(block_number))? {
			Some(justification) => return Ok(Some(FinalityProof {
				finalization_path,
				justification,
				authorities_proof,
			}.encode())),
			None if block_number == info.finalized_number => break,
			None => {
				block_number = block_number + One::one();
				current_header = blockchain.expect_header(BlockId::Number(block_number))?;
			},
		}
	}

	Err(ClientError::Backend(
		"cannot find justification for finalized block".into()
	).into())
}

/// Check proof-of-finality for the given block.
///
/// Returns the vector of headers (including `block` header, ordered by ASC block number) that MUST be
/// validated + imported at once (i.e. within single db transaction). If at least one of those headers
/// is invalid, all other MUST be considered invalid.
pub fn check_finality_proof<Block: BlockT<Hash=H256>, C>(
	check_execution_proof: C,
	parent_header: Block::Header,
	block: (NumberFor<Block>, Block::Hash),
	set_id: u64,
	remote_proof: Vec<u8>,
) -> ClientResult<Vec<Block::Header>>
	where
		NumberFor<Block>: grandpa::BlockNumberOps,
		C: Fn(&RemoteCallRequest<Block::Header>) -> ClientResult<Vec<u8>>,
{
	do_check_finality_proof::<Block, C, GrandpaJustification<Block>>(
		check_execution_proof,
		parent_header,
		block,
		set_id,
		remote_proof,
	)
}

/// Check proof-of-finality using given justification type.
fn do_check_finality_proof<Block: BlockT<Hash=H256>, C, J>(
	check_execution_proof: C,
	parent_header: Block::Header,
	block: (NumberFor<Block>, Block::Hash),
	set_id: u64,
	remote_proof: Vec<u8>,
) -> ClientResult<Vec<Block::Header>>
	where
		NumberFor<Block>: grandpa::BlockNumberOps,
		C: Fn(&RemoteCallRequest<Block::Header>) -> ClientResult<Vec<u8>>,
		J: ProvableJustification<Block::Header>,
{
	// decode finality proof
	let proof = FinalityProof::<Block::Header, J>::decode(&mut &remote_proof[..])
		.ok_or_else(|| ClientError::BadJustification("failed to decode finality proof".into()))?;

	// check that the first header in finalization path is the block itself
	{
		let finalized_header = proof.finalization_path.first()
			.ok_or_else(|| ClientError::from(ClientError::BadJustification(
				"finality proof: finalized path is empty".into()
			)))?;
		if *finalized_header.number() != block.0 || finalized_header.hash() != block.1 {
			return Err(ClientError::BadJustification(
				"finality proof: block is not a part of finalized path".into()
			).into());
		}
	}

	// check that the last header in finalization path is the justification target block
	let just_block = proof.justification.target_block();
	{
		let finalized_header = proof.finalization_path.last()
			.expect("checked above that proof.finalization_path is not empty; qed");
		if *finalized_header.number() != just_block.0 || finalized_header.hash() != just_block.1 {
			return Err(ClientError::BadJustification(
				"finality proof: target justification block is not a part of finalized path".into()
			).into());
		}
	}

	// check authorities set proof && get grandpa authorities that should have signed justification
	let grandpa_authorities = check_execution_proof(&RemoteCallRequest {
		block: just_block.1,
		header: parent_header,
		method: "GrandpaApi_grandpa_authorities".into(),
		call_data: vec![],
		retry_count: None,
	})?;
	let grandpa_authorities: Vec<(AuthorityId, u64)> = Decode::decode(&mut &grandpa_authorities[..])
		.ok_or_else(|| ClientError::BadJustification("failed to decode GRANDPA authorities set proof".into()))?;

	// and now check justification
	proof.justification.verify(set_id, &grandpa_authorities.into_iter().collect())?;

	telemetry!(CONSENSUS_INFO; "afg.finality_proof_ok";
		"set_id" => ?set_id, "finalized_header_hash" => ?block.1);
	Ok(proof.finalization_path)
}

/// Proof of finality.
///
/// Finality of block B is proved by providing:
/// 1) valid headers sub-chain from the block B to the block F;
/// 2) proof of `GrandpaApi::grandpa_authorities()` call at the block F;
/// 3) valid (with respect to proved authorities) GRANDPA justification of the block F.
#[derive(Debug, PartialEq, Encode, Decode)]
struct FinalityProof<Header, Justification> {
	/// Headers-path (ordered by block number, ascending) from the block we're gathering proof for
	/// (inclusive) to the target block of the justification (inclusive).
	pub finalization_path: Vec<Header>,
	/// Justification (finalization) of the last block from the `finalization_path`.
	pub justification: Justification,
	/// Proof of `GrandpaApi::grandpa_authorities` call execution at the
	/// justification' target block.
	pub authorities_proof: Vec<Vec<u8>>,
}

/// Justification used to prove block finality.
trait ProvableJustification<Header: HeaderT>: Encode + Decode {
	/// Get target block of this justification.
	fn target_block(&self) -> (Header::Number, Header::Hash);

	/// Verify justification with respect to authorities set and authorities set id.
	fn verify(&self, set_id: u64, authorities: &VoterSet<AuthorityId>) -> ClientResult<()>;
}

impl<Block: BlockT<Hash=H256>> ProvableJustification<Block::Header> for GrandpaJustification<Block>
	where
		NumberFor<Block>: BlockNumberOps,
{
	fn target_block(&self) -> (NumberFor<Block>, Block::Hash) {
		(self.commit.target_number, self.commit.target_hash)
	}

	fn verify(&self, set_id: u64, authorities: &VoterSet<AuthorityId>) -> ClientResult<()> {
		GrandpaJustification::verify(self, set_id, authorities)
	}
}

#[cfg(test)]
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

		fn verify(&self, set_id: u64, authorities: &VoterSet<AuthorityId>) -> ClientResult<()> {
			assert_eq!(set_id, 1);
			assert_eq!(authorities, &vec![
				(AuthorityId([1u8; 32]), 1),
				(AuthorityId([2u8; 32]), 2),
				(AuthorityId([3u8; 32]), 3),
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

			fn verify(&self, _set_id: u64, _authorities: &VoterSet<AuthorityId>) -> ClientResult<()> {
				Err(ClientError::Backend("test error".into()))
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
				(AuthorityId([1u8; 32]), 1u64),
				(AuthorityId([2u8; 32]), 2u64),
				(AuthorityId([3u8; 32]), 3u64),
			].encode()),
			header(1),
			(2, header(2).hash()),
			1,
			proof_of_2,
		).unwrap(), vec![header(2), header(3)]);
	}
}
