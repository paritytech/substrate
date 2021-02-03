// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use beefy_primitives::{self as bp, ValidatorSetId};

pub mod merkle_tree;
pub mod validator_set;

/// A marker struct for validator set merkle tree.
#[derive(Debug)]
pub struct ValidatorSetTree;

/// A marker struct for the MMR.
#[derive(Debug)]
pub struct Mmr;

#[derive(Debug, PartialEq, Eq)]
pub struct Payload {
	pub next_validator_set: Option<merkle_tree::Root<ValidatorSetTree>>,
	pub mmr: merkle_tree::Root<Mmr>,
}

impl Payload {
	pub fn new(root: u32) -> Self {
		Self {
			next_validator_set: None,
			mmr: root.into(),
		}
	}
}

pub type BlockNumber = u64;
pub type Commitment = bp::Commitment<BlockNumber, Payload>;
pub type SignedCommitment = bp::SignedCommitment<BlockNumber, Payload, validator_set::Signature>;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
	/// [Commitment] can't be imported, cause it's signed by either past or future validator set.
	InvalidValidatorSetId {
		expected: ValidatorSetId,
		got: ValidatorSetId,
	},
	/// [Commitment] can't be imported, cause it's a set transition block and the proof is missing.
	InvalidValidatorSetProof,
	/// [Commitment] is not useful, cause it's made for an older block than we know of.
	///
	/// In practice it's okay for the light client to import such commitments (if the validator set
	/// matches), but it doesn't provide any more value, since the payload is meant to be
	/// cumulative.
	/// It might be useful however, if we want to verify proofs that were generated against this
	/// specific block number.
	OldBlock {
		/// Best block currently known by the light client.
		best_known: BlockNumber,
		/// Block in the commitment.
		got: BlockNumber,
	},
	/// There are too many signatures in the commitment - more than validators.
	InvalidNumberOfSignatures {
		/// Number of validators in the set.
		expected: usize,
		/// Numbers of signatures in the commitment.
		got: usize,
	},
	/// [SignedCommitment] doesn't have enough valid signatures.
	NotEnoughValidSignatures {
		expected: usize,
		got: usize,
		valid: Option<usize>,
	},
	/// Next validator set has not been provided by any of the previous commitments.
	MissingNextValidatorSetData,
	/// Couldn't verify the proof against MMR root of the latest commitment.
	InvalidMmrProof,
}

type ValidatorSet = (ValidatorSetId, Vec<validator_set::Public>);

pub struct LightClient {
	validator_set: ValidatorSet,
	next_validator_set: Option<merkle_tree::Root<ValidatorSetTree>>,
	last_commitment: Option<Commitment>,
}

impl LightClient {
	pub fn import(&mut self, signed: SignedCommitment) -> Result<(), Error> {
		// Make sure it's not a set transition block (see [import_set_transition]).
		if signed.commitment.validator_set_id != self.validator_set.0 {
			return Err(Error::InvalidValidatorSetId {
				expected: self.validator_set.0,
				got: signed.commitment.validator_set_id,
			});
		}

		let commitment = self.validate_commitment(signed, &self.validator_set)?;
		if let Some(ref next_validator_set) = commitment.payload.next_validator_set {
			self.next_validator_set = Some(next_validator_set.clone());
		}
		self.last_commitment = Some(commitment);

		Ok(())
	}

	pub fn import_set_transition(
		&mut self,
		signed: SignedCommitment,
		validator_set_proof: merkle_tree::Proof<ValidatorSetTree, Vec<validator_set::Public>>,
	) -> Result<(), Error> {
		// Make sure it is a set transition block (see [import]).
		if signed.commitment.validator_set_id != self.validator_set.0 + 1 {
			return Err(Error::InvalidValidatorSetId {
				expected: self.validator_set.0 + 1,
				got: signed.commitment.validator_set_id,
			});
		}

		// verify validator set proof
		let validator_set_root = self
			.next_validator_set
			.as_ref()
			.ok_or(Error::MissingNextValidatorSetData)?;
		if !validator_set_proof.is_valid(validator_set_root) {
			return Err(Error::InvalidValidatorSetProof);
		}
		let set = validator_set_proof.into_data();
		let new_id = self.validator_set.0 + 1;
		let new_validator_set = (new_id, set);

		let commitment = self.validate_commitment(signed, &new_validator_set)?;

		self.validator_set = new_validator_set;
		self.next_validator_set = commitment.payload.next_validator_set.clone();
		self.last_commitment = Some(commitment);

		Ok(())
	}

	pub fn verify_proof<R>(&self, proof: merkle_tree::Proof<Mmr, R>) -> Result<R, Error> {
		if proof.is_valid(&self.last_payload().mmr) {
			Ok(proof.into_data())
		} else {
			Err(Error::InvalidMmrProof)
		}
	}

	pub fn validator_set(&self) -> &ValidatorSet {
		&self.validator_set
	}

	pub fn last_commitment(&self) -> Option<&Commitment> {
		self.last_commitment.as_ref()
	}

	pub fn last_payload(&self) -> &Payload {
		&self
			.last_commitment()
			.expect("Genesis doesn't contain commitment.")
			.payload
	}

	fn validate_commitment(
		&self,
		commitment: SignedCommitment,
		validator_set: &ValidatorSet,
	) -> Result<Commitment, Error> {
		let no_of_non_empty_signatures = commitment.no_of_signatures();
		let SignedCommitment { commitment, signatures } = commitment;
		// Make sure it's signed by the current validator set we know of.
		if validator_set.0 != commitment.validator_set_id {
			return Err(Error::InvalidValidatorSetId {
				expected: validator_set.0,
				got: commitment.validator_set_id,
			});
		}

		// Make sure it's not worse than what we already have.
		let best_block = self.last_commitment().map(|c| c.block_number).unwrap_or(0);
		if commitment.block_number <= best_block {
			return Err(Error::OldBlock {
				best_known: best_block,
				got: commitment.block_number,
			});
		}

		// check number of signatures
		let validator_set_count = validator_set.1.len();
		if signatures.len() != validator_set_count {
			return Err(Error::InvalidNumberOfSignatures {
				expected: validator_set_count,
				got: signatures.len(),
			});
		}

		// check the validity of signatures
		let minimal_number_of_signatures = Self::minimal_number_of_signatures(validator_set);
		if no_of_non_empty_signatures < minimal_number_of_signatures {
			return Err(Error::NotEnoughValidSignatures {
				expected: minimal_number_of_signatures,
				got: no_of_non_empty_signatures,
				valid: None,
			});
		}

		let mut valid = 0;
		for (signature, public) in signatures.into_iter().zip(validator_set.1.iter()) {
			match signature {
				Some(signature) if signature.is_valid_for(&public) => {
					valid += 1;
				}
				_ => {}
			}
		}

		if valid < minimal_number_of_signatures {
			return Err(Error::NotEnoughValidSignatures {
				expected: minimal_number_of_signatures,
				got: no_of_non_empty_signatures,
				valid: Some(valid),
			});
		}

		Ok(commitment)
	}

	fn minimal_number_of_signatures(set: &ValidatorSet) -> usize {
		2 * set.1.len() / 3 + 1
	}
}

pub fn new() -> LightClient {
	LightClient {
		validator_set: (0, vec![validator_set::Public(0)]),
		next_validator_set: None,
		last_commitment: None,
	}
}
