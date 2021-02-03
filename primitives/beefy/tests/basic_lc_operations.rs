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

mod light_client;

use self::light_client::{validator_set, Commitment, Error, Payload, SignedCommitment};

#[test]
fn light_client_should_make_progress() {
	// given
	let mut lc = light_client::new();

	// when
	let result = lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 2,
			validator_set_id: 0,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(0.into()))],
	});

	// then
	assert_eq!(result, Ok(()));
	assert_eq!(lc.last_payload(), &Payload::new(1));
}

#[test]
fn should_verify_mmr_proof() {
	// given
	let mut lc = light_client::new();
	lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 2,
			validator_set_id: 0,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(0.into()))],
	})
	.unwrap();

	// when
	let result = lc.verify_proof(light_client::merkle_tree::Proof::ValidFor(1.into(), ()));

	// then
	assert_eq!(result, Ok(()));
}

#[test]
fn should_reject_invalid_mmr_proof() {
	// given
	let mut lc = light_client::new();
	lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 2,
			validator_set_id: 0,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(0.into()))],
	})
	.unwrap();

	// when
	let result = lc.verify_proof(light_client::merkle_tree::Proof::Invalid(()));

	// then
	assert_eq!(result, Err(Error::InvalidMmrProof));
}

#[test]
fn light_client_should_reject_invalid_validator_set() {
	// given
	let mut lc = light_client::new();

	// when
	let result = lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 1,
			validator_set_id: 1,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(0.into()))],
	});

	// then
	assert_eq!(result, Err(Error::InvalidValidatorSetId { expected: 0, got: 1 }));
	assert_eq!(lc.last_commitment(), None);
}

#[test]
fn light_client_should_reject_set_transitions_without_validator_proof() {
	// given
	let mut lc = light_client::new();

	// when
	let result = lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 1,
			validator_set_id: 1,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(0.into()))],
	});

	// then
	assert_eq!(result, Err(Error::InvalidValidatorSetId { expected: 0, got: 1 }));
	assert_eq!(lc.last_commitment(), None);
}

#[test]
fn light_client_should_reject_older_block() {
	// given
	let mut lc = light_client::new();
	// jump to 10
	lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 10,
			validator_set_id: 0,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(0.into()))],
	})
	.unwrap();

	// when
	let result = lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 5,
			validator_set_id: 0,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(0.into()))],
	});

	// then
	assert_eq!(result, Err(Error::OldBlock { best_known: 10, got: 5 }));
}

#[test]
fn light_client_should_reject_if_not_enough_signatures() {
	// given
	let mut lc = light_client::new();

	// when
	let result = lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 5,
			validator_set_id: 0,
		},
		signatures: vec![None],
	});

	// then
	assert_eq!(
		result,
		Err(Error::NotEnoughValidSignatures {
			expected: 1,
			got: 0,
			valid: None,
		})
	);
}

#[test]
fn light_client_should_reject_if_too_many_or_too_little_signatures() {
	// given
	let mut lc = light_client::new();

	// when
	let result = lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 5,
			validator_set_id: 0,
		},
		signatures: vec![None, None],
	});
	let result2 = lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 5,
			validator_set_id: 0,
		},
		signatures: vec![],
	});

	// then
	assert_eq!(result, Err(Error::InvalidNumberOfSignatures { expected: 1, got: 2 }));
	assert_eq!(result2, Err(Error::InvalidNumberOfSignatures { expected: 1, got: 0 }));
}

#[test]
fn light_client_should_reject_if_not_enough_valid_signatures() {
	// given
	let mut lc = light_client::new();

	// when
	let result = lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 5,
			validator_set_id: 0,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(1.into()))],
	});

	// then
	assert_eq!(
		result,
		Err(Error::NotEnoughValidSignatures {
			expected: 1,
			got: 1,
			valid: Some(0),
		})
	);

	// when
	let result = lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload::new(1),
			block_number: 5,
			validator_set_id: 0,
		},
		signatures: vec![Some(validator_set::Signature::Invalid)],
	});

	// then
	assert_eq!(
		result,
		Err(Error::NotEnoughValidSignatures {
			expected: 1,
			got: 1,
			valid: Some(0),
		})
	);
}

#[test]
fn light_client_should_perform_set_transition() {
	// given
	let mut lc = light_client::new();
	lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload {
				next_validator_set: Some(2.into()),
				mmr: 1.into(),
			},
			block_number: 5,
			validator_set_id: 0,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(0.into()))],
	})
	.unwrap();

	let commitment = SignedCommitment {
		commitment: Commitment {
			payload: Payload {
				next_validator_set: None,
				mmr: 1.into(),
			},
			block_number: 6,
			validator_set_id: 1,
		},
		signatures: vec![
			Some(validator_set::Signature::ValidFor(1.into())),
			Some(validator_set::Signature::ValidFor(2.into())),
		],
	};

	// when
	let result = lc.import_set_transition(
		commitment,
		light_client::merkle_tree::Proof::ValidFor(2.into(), vec![1.into(), 2.into()]),
	);

	// then
	assert_eq!(result, Ok(()));
	assert_eq!(lc.validator_set(), &(1, vec![1.into(), 2.into()],));
}

#[test]
fn light_client_reject_set_transition_with_invalid_payload() {
	// given
	let mut lc = light_client::new();
	let commitment = SignedCommitment {
		commitment: Commitment {
			payload: Payload {
				// missing validator set in the payload
				next_validator_set: None,
				mmr: 1.into(),
			},
			block_number: 5,
			validator_set_id: 1,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(0.into()))],
	};

	// when
	let result = lc.import_set_transition(
		commitment,
		light_client::merkle_tree::Proof::ValidFor(2.into(), vec![0.into(), 1.into(), 2.into()]),
	);

	// then
	assert_eq!(result, Err(Error::MissingNextValidatorSetData));
}

#[test]
fn light_client_reject_set_transition_with_invalid_proof() {
	// given
	let mut lc = light_client::new();
	lc.import(SignedCommitment {
		commitment: Commitment {
			payload: Payload {
				next_validator_set: Some(1.into()),
				mmr: 0.into(),
			},
			block_number: 3,
			validator_set_id: 0,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(0.into()))],
	})
	.unwrap();
	let commitment = SignedCommitment {
		commitment: Commitment {
			payload: Payload {
				next_validator_set: None,
				mmr: 1.into(),
			},
			block_number: 5,
			validator_set_id: 1,
		},
		signatures: vec![Some(validator_set::Signature::ValidFor(0.into()))],
	};

	// when
	let result = lc.import_set_transition(
		commitment,
		light_client::merkle_tree::Proof::ValidFor(2.into(), vec![0.into(), 1.into(), 2.into()]),
	);

	// then
	assert_eq!(result, Err(Error::InvalidValidatorSetProof));
}
