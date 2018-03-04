// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Utility for substrate-based runtimes that want to check misbehavior reports.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_io as runtime_io;

#[cfg(test)]
extern crate substrate_bft;
#[cfg(test)]
extern crate substrate_keyring as keyring;

use codec::Slicable;
use primitives::{AuthorityId, Signature};
use primitives::block::HeaderHash;
use	primitives::bft::{Action, Message, MisbehaviorKind};

// check a message signature. returns true if signed by that authority.
fn check_message_sig(message: Message, signature: &Signature, from: &AuthorityId) -> bool {
	let msg = message.encode();
	runtime_io::ed25519_verify(&signature.0, &msg, from)
}

fn prepare(parent: HeaderHash, round_number: u32, hash: HeaderHash) -> Message {
	Message {
		parent,
		action: Action::Prepare(round_number, hash),
	}
}

fn commit(parent: HeaderHash, round_number: u32, hash: HeaderHash) -> Message {
	Message {
		parent,
		action: Action::Commit(round_number, hash),
	}
}

/// Evaluate misbehavior.
///
/// Doesn't check that the header hash in question is
/// valid or whether the misbehaving authority was part of
/// the set at that block.
pub fn evaluate_misbehavior(
	misbehaved: &AuthorityId,
	parent_hash: HeaderHash,
	kind: &MisbehaviorKind,
) -> bool {
	match *kind {
		MisbehaviorKind::BftDoublePrepare(round, (h_1, ref s_1), (h_2, ref s_2)) => {
			s_1 != s_2 &&
			check_message_sig(prepare(parent_hash, round, h_1), s_1, misbehaved) &&
			check_message_sig(prepare(parent_hash, round, h_2), s_2, misbehaved)
		}
		MisbehaviorKind::BftDoubleCommit(round, (h_1, ref s_1), (h_2, ref s_2)) => {
			s_1 != s_2 &&
			check_message_sig(commit(parent_hash, round, h_1), s_1, misbehaved) &&
			check_message_sig(commit(parent_hash, round, h_2), s_2, misbehaved)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use substrate_bft::generic;
	use keyring::ed25519;
	use keyring::Keyring;

	fn sign_prepare(key: &ed25519::Pair, round: u32, hash: HeaderHash, parent_hash: HeaderHash) -> (HeaderHash, Signature) {
		let msg = substrate_bft::sign_message(
			generic::Message::Vote(generic::Vote::Prepare(round as _, hash)),
			key,
			parent_hash
		);

		match msg {
			generic::LocalizedMessage::Vote(vote) => (hash, vote.signature.signature),
			_ => panic!("signing vote leads to signed vote"),
		}
	}

	fn sign_commit(key: &ed25519::Pair, round: u32, hash: HeaderHash, parent_hash: HeaderHash) -> (HeaderHash, Signature) {
		let msg = substrate_bft::sign_message(
			generic::Message::Vote(generic::Vote::Commit(round as _, hash)),
			key,
			parent_hash
		);

		match msg {
			generic::LocalizedMessage::Vote(vote) => (hash, vote.signature.signature),
			_ => panic!("signing vote leads to signed vote"),
		}
	}

	#[test]
	fn evaluates_double_prepare() {
		let key: ed25519::Pair = Keyring::One.into();
		let parent_hash = [0xff; 32].into();
		let hash_1 = [0; 32].into();
		let hash_2 = [1; 32].into();

		assert!(evaluate_misbehavior(
			&key.public().0,
			parent_hash,
			&MisbehaviorKind::BftDoublePrepare(
				1,
				sign_prepare(&key, 1, hash_1, parent_hash),
				sign_prepare(&key, 1, hash_2, parent_hash)
			)
		));

		// same signature twice is not misbehavior.
		let signed = sign_prepare(&key, 1, hash_1, parent_hash);
		assert!(evaluate_misbehavior(
			&key.public().0,
			parent_hash,
			&MisbehaviorKind::BftDoublePrepare(
				1,
				signed,
				signed,
			)
		) == false);

		// misbehavior has wrong target.
		assert!(evaluate_misbehavior(
			&Keyring::Two.to_raw_public(),
			parent_hash,
			&MisbehaviorKind::BftDoublePrepare(
				1,
				sign_prepare(&key, 1, hash_1, parent_hash),
				sign_prepare(&key, 1, hash_2, parent_hash),
			)
		) == false);
	}

	#[test]
	fn evaluates_double_commit() {
		let key: ed25519::Pair = Keyring::One.into();
		let parent_hash = [0xff; 32].into();
		let hash_1 = [0; 32].into();
		let hash_2 = [1; 32].into();

		assert!(evaluate_misbehavior(
			&key.public().0,
			parent_hash,
			&MisbehaviorKind::BftDoubleCommit(
				1,
				sign_commit(&key, 1, hash_1, parent_hash),
				sign_commit(&key, 1, hash_2, parent_hash)
			)
		));

		// same signature twice is not misbehavior.
		let signed = sign_commit(&key, 1, hash_1, parent_hash);
		assert!(evaluate_misbehavior(
			&key.public().0,
			parent_hash,
			&MisbehaviorKind::BftDoubleCommit(
				1,
				signed,
				signed,
			)
		) == false);

		// misbehavior has wrong target.
		assert!(evaluate_misbehavior(
			&Keyring::Two.to_raw_public(),
			parent_hash,
			&MisbehaviorKind::BftDoubleCommit(
				1,
				sign_commit(&key, 1, hash_1, parent_hash),
				sign_commit(&key, 1, hash_2, parent_hash),
			)
		) == false);
	}
}
