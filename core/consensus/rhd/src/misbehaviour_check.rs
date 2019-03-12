// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Utility for substrate-based runtimes that want to check misbehavior reports.

use codec::{Codec, Encode};
use primitives::{AuthorityId, Signature};

use rhododendron::messages::{Action, Message, MisbehaviorKind};
use runtime_io;

// check a message signature. returns true if signed by that authority.
fn check_message_sig<B: Codec, H: Codec>(
	message: Message<B, H>,
	signature: &Signature,
	from: &AuthorityId
) -> bool {
	let msg: Vec<u8> = message.encode();
	runtime_io::ed25519_verify(&signature.0, &msg, from)
}

fn prepare<B, H>(parent: H, round_number: u32, hash: H) -> Message<B, H> {
	Message {
		parent,
		action: Action::Prepare(round_number, hash),
	}
}

fn commit<B, H>(parent: H, round_number: u32, hash: H) -> Message<B, H> {
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
pub fn evaluate_misbehavior<B: Codec, H: Codec + Copy>(
	misbehaved: &AuthorityId,
	parent_hash: H,
	kind: &MisbehaviorKind<H>,
) -> bool {
	match *kind {
		MisbehaviorKind::BftDoublePrepare(round, (h_1, ref s_1), (h_2, ref s_2)) => {
			s_1 != s_2 &&
			check_message_sig::<B, H>(prepare::<B, H>(parent_hash, round, h_1), s_1, misbehaved) &&
			check_message_sig::<B, H>(prepare::<B, H>(parent_hash, round, h_2), s_2, misbehaved)
		}
		MisbehaviorKind::BftDoubleCommit(round, (h_1, ref s_1), (h_2, ref s_2)) => {
			s_1 != s_2 &&
			check_message_sig::<B, H>(commit::<B, H>(parent_hash, round, h_1), s_1, misbehaved) &&
			check_message_sig::<B, H>(commit::<B, H>(parent_hash, round, h_2), s_2, misbehaved)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use keyring::AuthorityKeyring;
	use rhododendron;

	use runtime_primitives::testing::{H256, Block as RawBlock};

	type Block = RawBlock<u64>;

	fn sign_prepare(key: &ed25519::Pair, round: u32, hash: H256, parent_hash: H256) -> (H256, Signature) {
		let msg = ::sign_message::<Block>(
			rhododendron::Message::Vote(rhododendron::Vote::Prepare(round as _, hash)),
			key,
			parent_hash
		);

		match msg {
			rhododendron::LocalizedMessage::Vote(vote) => (hash, vote.signature.signature),
			_ => panic!("signing vote leads to signed vote"),
		}
	}

	fn sign_commit(key: &ed25519::Pair, round: u32, hash: H256, parent_hash: H256) -> (H256, Signature) {
		let msg = ::sign_message::<Block>(
			rhododendron::Message::Vote(rhododendron::Vote::Commit(round as _, hash)),
			key,
			parent_hash
		);

		match msg {
			rhododendron::LocalizedMessage::Vote(vote) => (hash, vote.signature.signature),
			_ => panic!("signing vote leads to signed vote"),
		}
	}

	#[test]
	fn evaluates_double_prepare() {
		let key = AuthorityKeyring::One.pair();
		let parent_hash = [0xff; 32].into();
		let hash_1 = [0; 32].into();
		let hash_2 = [1; 32].into();

		assert!(evaluate_misbehavior::<Block, H256>(
			&key.public().into(),
			parent_hash,
			&MisbehaviorKind::BftDoublePrepare(
				1,
				sign_prepare(&key, 1, hash_1, parent_hash),
				sign_prepare(&key, 1, hash_2, parent_hash)
			)
		));

		// same signature twice is not misbehavior.
		let signed = sign_prepare(&key, 1, hash_1, parent_hash);
		assert!(!evaluate_misbehavior::<Block, H256>(
			&key.public().into(),
			parent_hash,
			&MisbehaviorKind::BftDoublePrepare(
				1,
				signed,
				signed,
			)
		));

		// misbehavior has wrong target.
		assert!(!evaluate_misbehavior::<Block, H256>(
			&AuthorityKeyring::Two.into(),
			parent_hash,
			&MisbehaviorKind::BftDoublePrepare(
				1,
				sign_prepare(&key, 1, hash_1, parent_hash),
				sign_prepare(&key, 1, hash_2, parent_hash),
			)
		));
	}

	#[test]
	fn evaluates_double_commit() {
		let key = AuthorityKeyring::One.pair();
		let parent_hash = [0xff; 32].into();
		let hash_1 = [0; 32].into();
		let hash_2 = [1; 32].into();

		assert!(evaluate_misbehavior::<Block, H256>(
			&key.public().into(),
			parent_hash,
			&MisbehaviorKind::BftDoubleCommit(
				1,
				sign_commit(&key, 1, hash_1, parent_hash),
				sign_commit(&key, 1, hash_2, parent_hash)
			)
		));

		// same signature twice is not misbehavior.
		let signed = sign_commit(&key, 1, hash_1, parent_hash);
		assert!(!evaluate_misbehavior::<Block, H256>(
			&key.public().into(),
			parent_hash,
			&MisbehaviorKind::BftDoubleCommit(
				1,
				signed,
				signed,
			)
		));

		// misbehavior has wrong target.
		assert!(!evaluate_misbehavior::<Block, H256>(
			&AuthorityKeyring::Two.into(),
			parent_hash,
			&MisbehaviorKind::BftDoubleCommit(
				1,
				sign_commit(&key, 1, hash_1, parent_hash),
				sign_commit(&key, 1, hash_2, parent_hash),
			)
		));
	}
}
