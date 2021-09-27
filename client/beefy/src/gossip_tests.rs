// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use sc_keystore::LocalKeystore;
use sc_network_test::Block;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};

use beefy_primitives::{crypto::Signature, Commitment, MmrRootHash, VoteMessage, KEY_TYPE};

use crate::keystore::{tests::Keyring, BeefyKeystore};

use super::*;

#[test]
fn note_round_works() {
	let gv = GossipValidator::<Block>::new();

	gv.note_round(1u64);

	let live = gv.known_votes.read();
	assert!(GossipValidator::<Block>::is_live(&live, &1u64));

	drop(live);

	gv.note_round(3u64);
	gv.note_round(7u64);
	gv.note_round(10u64);

	let live = gv.known_votes.read();

	assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

	assert!(!GossipValidator::<Block>::is_live(&live, &1u64));
	assert!(GossipValidator::<Block>::is_live(&live, &3u64));
	assert!(GossipValidator::<Block>::is_live(&live, &7u64));
	assert!(GossipValidator::<Block>::is_live(&live, &10u64));
}

#[test]
fn keeps_most_recent_max_rounds() {
	let gv = GossipValidator::<Block>::new();

	gv.note_round(3u64);
	gv.note_round(7u64);
	gv.note_round(10u64);
	gv.note_round(1u64);

	let live = gv.known_votes.read();

	assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

	assert!(GossipValidator::<Block>::is_live(&live, &3u64));
	assert!(!GossipValidator::<Block>::is_live(&live, &1u64));

	drop(live);

	gv.note_round(23u64);
	gv.note_round(15u64);
	gv.note_round(20u64);
	gv.note_round(2u64);

	let live = gv.known_votes.read();

	assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

	assert!(GossipValidator::<Block>::is_live(&live, &15u64));
	assert!(GossipValidator::<Block>::is_live(&live, &20u64));
	assert!(GossipValidator::<Block>::is_live(&live, &23u64));
}

#[test]
fn note_same_round_twice() {
	let gv = GossipValidator::<Block>::new();

	gv.note_round(3u64);
	gv.note_round(7u64);
	gv.note_round(10u64);

	let live = gv.known_votes.read();

	assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

	drop(live);

	// note round #7 again -> should not change anything
	gv.note_round(7u64);

	let live = gv.known_votes.read();

	assert_eq!(live.len(), MAX_LIVE_GOSSIP_ROUNDS);

	assert!(GossipValidator::<Block>::is_live(&live, &3u64));
	assert!(GossipValidator::<Block>::is_live(&live, &7u64));
	assert!(GossipValidator::<Block>::is_live(&live, &10u64));
}

struct TestContext;
impl<B: sp_runtime::traits::Block> ValidatorContext<B> for TestContext {
	fn broadcast_topic(&mut self, _topic: B::Hash, _force: bool) {
		todo!()
	}

	fn broadcast_message(&mut self, _topic: B::Hash, _message: Vec<u8>, _force: bool) {
		todo!()
	}

	fn send_message(&mut self, _who: &sc_network::PeerId, _message: Vec<u8>) {
		todo!()
	}

	fn send_topic(&mut self, _who: &sc_network::PeerId, _topic: B::Hash, _force: bool) {
		todo!()
	}
}

fn sign_commitment<BN: Encode, P: Encode>(
	who: &Keyring,
	commitment: &Commitment<BN, P>,
) -> Signature {
	let store: SyncCryptoStorePtr = std::sync::Arc::new(LocalKeystore::in_memory());
	SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&who.to_seed())).unwrap();
	let beefy_keystore: BeefyKeystore = Some(store).into();

	beefy_keystore.sign(&who.public(), &commitment.encode()).unwrap()
}

#[test]
fn should_avoid_verifying_signatures_twice() {
	let gv = GossipValidator::<Block>::new();
	let sender = sc_network::PeerId::random();
	let mut context = TestContext;

	let commitment =
		Commitment { payload: MmrRootHash::default(), block_number: 3_u64, validator_set_id: 0 };

	let signature = sign_commitment(&Keyring::Alice, &commitment);

	let vote = VoteMessage { commitment, id: Keyring::Alice.public(), signature };

	gv.note_round(3u64);
	gv.note_round(7u64);
	gv.note_round(10u64);

	// first time the cache should be populated.
	let res = gv.validate(&mut context, &sender, &vote.encode());

	assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));
	assert_eq!(gv.known_votes.read().get(&vote.commitment.block_number).map(|x| x.len()), Some(1));

	// second time we should hit the cache
	let res = gv.validate(&mut context, &sender, &vote.encode());

	assert!(matches!(res, ValidationResult::ProcessAndKeep(_)));

	// next we should quickly reject if the round is not live.
	gv.note_round(11_u64);
	gv.note_round(12_u64);

	assert!(!GossipValidator::<Block>::is_live(
		&*gv.known_votes.read(),
		&vote.commitment.block_number
	));

	let res = gv.validate(&mut context, &sender, &vote.encode());

	assert!(matches!(res, ValidationResult::Discard));
}
