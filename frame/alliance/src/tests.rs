// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Tests for the alliance pallet.

use sp_runtime::traits::Hash;

use frame_support::{assert_noop, assert_ok, Hashable};
use frame_system::{EventRecord, Phase};

use super::*;
use crate::mock::*;

type AllianceMotionEvent = pallet_collective::Event<Test, pallet_collective::Instance1>;

#[test]
fn propose_works() {
	new_test_ext().execute_with(|| {
		let proposal = make_proposal(42);
		let hash: H256 = proposal.blake2_256().into();

		// only votable member can propose proposal, 4 is ally not have vote rights
		assert_noop!(
			Alliance::propose(Origin::signed(4), Box::new(proposal.clone())),
			Error::<Test, ()>::NotVotableMember
		);

		assert_ok!(Alliance::propose(Origin::signed(1), Box::new(proposal.clone())));
		assert_eq!(*AllianceMotion::proposals(), vec![hash]);
		assert_eq!(AllianceMotion::proposal_of(&hash), Some(proposal));
		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::Initialization,
				event: mock::Event::AllianceMotion(AllianceMotionEvent::Proposed(1, 0, hash, 3)),
				topics: vec![],
			}]
		);
	});
}

#[test]
fn vote_works() {
	new_test_ext().execute_with(|| {
		let proposal = make_proposal(42);
		let hash: H256 = proposal.blake2_256().into();
		assert_ok!(Alliance::propose(Origin::signed(1), Box::new(proposal.clone())));
		assert_ok!(Alliance::vote(Origin::signed(2), hash.clone(), 0, true));

		let record = |event| EventRecord { phase: Phase::Initialization, event, topics: vec![] };
		assert_eq!(
			System::events(),
			vec![
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Proposed(
					1,
					0,
					hash.clone(),
					3
				))),
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Voted(
					2,
					hash.clone(),
					true,
					1,
					0
				))),
			]
		);
	});
}

#[test]
fn veto_works() {
	new_test_ext().execute_with(|| {
		let proposal = make_proposal(42);
		let hash: H256 = proposal.blake2_256().into();
		assert_ok!(Alliance::propose(Origin::signed(1), Box::new(proposal.clone())));
		// only set_rule/elevate_ally can be veto
		assert_noop!(
			Alliance::veto(Origin::signed(1), hash.clone()),
			Error::<Test, ()>::NotVetoableProposal
		);

		let cid = test_cid();
		let vetoable_proposal = make_set_rule_proposal(cid);
		let vetoable_hash: H256 = vetoable_proposal.blake2_256().into();
		assert_ok!(Alliance::propose(Origin::signed(1), Box::new(vetoable_proposal.clone())));

		// only founder have veto rights, 3 is fellow
		assert_noop!(
			Alliance::veto(Origin::signed(3), vetoable_hash.clone()),
			Error::<Test, ()>::NotFounder
		);

		assert_ok!(Alliance::veto(Origin::signed(2), vetoable_hash.clone()));
		let record = |event| EventRecord { phase: Phase::Initialization, event, topics: vec![] };
		assert_eq!(
			System::events(),
			vec![
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Proposed(
					1,
					0,
					hash.clone(),
					3
				))),
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Proposed(
					1,
					1,
					vetoable_hash.clone(),
					3
				))),
				// record(mock::Event::AllianceMotion(AllianceMotionEvent::Voted(2, hash.clone(),
				// true, 2, 0))),
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Disapproved(
					vetoable_hash.clone()
				))),
			]
		);
	})
}

#[test]
fn close_works() {
	new_test_ext().execute_with(|| {
		let proposal = make_proposal(42);
		let proposal_len: u32 = proposal.using_encoded(|p| p.len() as u32);
		let proposal_weight = proposal.get_dispatch_info().weight;
		let hash = BlakeTwo256::hash_of(&proposal);
		assert_ok!(Alliance::propose(Origin::signed(1), Box::new(proposal.clone())));
		assert_ok!(Alliance::vote(Origin::signed(1), hash.clone(), 0, true));
		assert_ok!(Alliance::vote(Origin::signed(2), hash.clone(), 0, true));
		assert_ok!(Alliance::vote(Origin::signed(3), hash.clone(), 0, true));
		assert_ok!(Alliance::close(
			Origin::signed(1),
			hash.clone(),
			0,
			proposal_weight,
			proposal_len
		));

		let record = |event| EventRecord { phase: Phase::Initialization, event, topics: vec![] };
		assert_eq!(
			System::events(),
			vec![
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Proposed(
					1,
					0,
					hash.clone(),
					3
				))),
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Voted(
					1,
					hash.clone(),
					true,
					1,
					0
				))),
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Voted(
					2,
					hash.clone(),
					true,
					2,
					0
				))),
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Voted(
					3,
					hash.clone(),
					true,
					3,
					0
				))),
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Closed(
					hash.clone(),
					3,
					0
				))),
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Approved(hash.clone()))),
				record(mock::Event::AllianceMotion(AllianceMotionEvent::Executed(
					hash.clone(),
					Err(DispatchError::BadOrigin)
				)))
			]
		);
	});
}

#[test]
fn set_rule_works() {
	new_test_ext().execute_with(|| {
		let cid = test_cid();
		assert_ok!(Alliance::set_rule(Origin::signed(1), cid));
		assert_eq!(Alliance::rule(), Some(cid));

		System::assert_last_event(mock::Event::Alliance(crate::Event::NewRule(cid)));
	});
}

#[test]
fn announce_works() {
	new_test_ext().execute_with(|| {
		let cid = test_cid();
		assert_ok!(Alliance::announce(Origin::signed(1), cid));
		assert_eq!(Alliance::announcements(), vec![cid]);

		System::assert_last_event(mock::Event::Alliance(crate::Event::NewAnnouncement(cid)));
	});
}

#[test]
fn remove_announcement_works() {
	new_test_ext().execute_with(|| {
		let cid = test_cid();
		assert_ok!(Alliance::announce(Origin::signed(1), cid));
		assert_eq!(Alliance::announcements(), vec![cid]);
		System::assert_last_event(mock::Event::Alliance(crate::Event::NewAnnouncement(cid)));

		System::set_block_number(2);

		assert_ok!(Alliance::remove_announcement(Origin::signed(1), cid));
		assert_eq!(Alliance::announcements(), vec![]);
		System::assert_last_event(mock::Event::Alliance(crate::Event::AnnouncementRemoved(cid)));
	});
}

#[test]
fn submit_candidacy_works() {
	new_test_ext().execute_with(|| {
		// check already member
		assert_noop!(
			Alliance::submit_candidacy(Origin::signed(1)),
			Error::<Test, ()>::AlreadyMember
		);

		// check already in blacklist
		assert_ok!(Alliance::add_blacklist(Origin::signed(1), vec![BlacklistItem::AccountId(4)]));
		assert_noop!(
			Alliance::submit_candidacy(Origin::signed(4)),
			Error::<Test, ()>::AlreadyInBlacklist
		);
		assert_ok!(Alliance::remove_blacklist(
			Origin::signed(1),
			vec![BlacklistItem::AccountId(4)]
		));

		// check deposit funds
		assert_noop!(
			Alliance::submit_candidacy(Origin::signed(5)),
			Error::<Test, ()>::InsufficientCandidateFunds
		);

		// success to submit
		assert_ok!(Alliance::submit_candidacy(Origin::signed(4)));
		assert_eq!(Alliance::deposit_of(4), Some(25));
		assert_eq!(Alliance::candidates(), vec![4]);

		// check already candidate
		assert_noop!(
			Alliance::submit_candidacy(Origin::signed(4)),
			Error::<Test, ()>::AlreadyCandidate
		);
	});
}

#[test]
fn nominate_candidacy_works() {
	new_test_ext().execute_with(|| {
		// check already member
		assert_noop!(
			Alliance::nominate_candidacy(Origin::signed(1), 2),
			Error::<Test, ()>::AlreadyMember
		);

		// only votable member(founder/fellow) have nominate right
		assert_noop!(
			Alliance::nominate_candidacy(Origin::signed(5), 4),
			Error::<Test, ()>::NotVotableMember
		);

		// check already in blacklist
		assert_ok!(Alliance::add_blacklist(Origin::signed(1), vec![BlacklistItem::AccountId(4)]));
		assert_noop!(
			Alliance::nominate_candidacy(Origin::signed(1), 4),
			Error::<Test, ()>::AlreadyInBlacklist
		);
		assert_ok!(Alliance::remove_blacklist(
			Origin::signed(1),
			vec![BlacklistItem::AccountId(4)]
		));

		// success to nominate
		assert_ok!(Alliance::nominate_candidacy(Origin::signed(1), 4));
		assert_eq!(Alliance::deposit_of(4), None);
		assert_eq!(Alliance::candidates(), vec![4]);

		// check already candidate
		assert_noop!(
			Alliance::nominate_candidacy(Origin::signed(1), 4),
			Error::<Test, ()>::AlreadyCandidate
		);
	});
}

#[test]
fn approve_candidate_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Alliance::approve_candidate(Origin::signed(1), 4),
			Error::<Test, ()>::NotCandidate
		);

		assert_ok!(Alliance::submit_candidacy(Origin::signed(4)));
		assert_eq!(Alliance::candidates(), vec![4]);

		assert_ok!(Alliance::approve_candidate(Origin::signed(1), 4));
		assert_eq!(Alliance::candidates(), Vec::<u64>::new());
		assert_eq!(Alliance::members(MemberRole::Ally), vec![4]);
	});
}

#[test]
fn reject_candidate_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Alliance::reject_candidate(Origin::signed(1), 4),
			Error::<Test, ()>::NotCandidate
		);

		assert_ok!(Alliance::submit_candidacy(Origin::signed(4)));
		assert_eq!(Alliance::deposit_of(4), Some(25));
		assert_eq!(Alliance::candidates(), vec![4]);

		assert_ok!(Alliance::reject_candidate(Origin::signed(1), 4));
		assert_eq!(Alliance::deposit_of(4), None);
		assert_eq!(Alliance::candidates(), Vec::<u64>::new());
	});
}

#[test]
fn elevate_ally_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(Alliance::elevate_ally(Origin::signed(1), 4), Error::<Test, ()>::NotAlly);

		assert_ok!(Alliance::submit_candidacy(Origin::signed(4)));
		assert_ok!(Alliance::approve_candidate(Origin::signed(1), 4));
		assert_eq!(Alliance::members(MemberRole::Ally), vec![4]);
		assert_eq!(Alliance::members(MemberRole::Fellow), vec![3]);

		assert_ok!(Alliance::elevate_ally(Origin::signed(1), 4));
		assert_eq!(Alliance::members(MemberRole::Ally), Vec::<u64>::new());
		assert_eq!(Alliance::members(MemberRole::Fellow), vec![3, 4]);
	});
}

#[test]
fn retire_works() {
	new_test_ext().execute_with(|| {
		let proposal = make_kick_member_proposal(2);
		assert_ok!(Alliance::propose(Origin::signed(1), Box::new(proposal.clone())));
		assert_noop!(Alliance::retire(Origin::signed(2)), Error::<Test, ()>::KickingMember);

		assert_noop!(Alliance::retire(Origin::signed(4)), Error::<Test, ()>::NotMember);

		assert_eq!(Alliance::members(MemberRole::Fellow), vec![3]);
		assert_ok!(Alliance::retire(Origin::signed(3)));
		assert_eq!(Alliance::members(MemberRole::Fellow), Vec::<u64>::new());
	});
}

#[test]
fn kick_member_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Alliance::kick_member(Origin::signed(1), 2),
			Error::<Test, ()>::NotKickingMember
		);

		let proposal = make_kick_member_proposal(2);
		assert_ok!(Alliance::propose(Origin::signed(1), Box::new(proposal.clone())));
		assert_eq!(Alliance::kicking_member(2), true);
		assert_eq!(Alliance::members(MemberRole::Founder), vec![1, 2]);

		assert_ok!(Alliance::kick_member(Origin::signed(1), 2));
		assert_eq!(Alliance::members(MemberRole::Founder), vec![1]);
	});
}

#[test]
fn add_blacklist_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Alliance::add_blacklist(
			Origin::signed(1),
			vec![BlacklistItem::AccountId(3), BlacklistItem::Website("abc".as_bytes().to_vec())]
		));
		assert_eq!(Alliance::account_blacklist(), vec![3]);
		assert_eq!(Alliance::website_blacklist(), vec!["abc".as_bytes().to_vec()]);

		assert_noop!(
			Alliance::add_blacklist(Origin::signed(1), vec![BlacklistItem::AccountId(3)]),
			Error::<Test, ()>::AlreadyInBlacklist
		);
	});
}

#[test]
fn remove_blacklist_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Alliance::remove_blacklist(Origin::signed(1), vec![BlacklistItem::AccountId(3)]),
			Error::<Test, ()>::NotInBlacklist
		);

		assert_ok!(Alliance::add_blacklist(Origin::signed(1), vec![BlacklistItem::AccountId(3)]));
		assert_eq!(Alliance::account_blacklist(), vec![3]);
		assert_ok!(Alliance::remove_blacklist(
			Origin::signed(1),
			vec![BlacklistItem::AccountId(3)]
		));
		assert_eq!(Alliance::account_blacklist(), Vec::<u64>::new());
	});
}

mod cid_tests {
	use cid::{
		multibase::Base,
		multihash::{Code, MultihashDigest},
		Cid, Version,
	};
	use codec::{Decode, Encode};
	use hex_literal::hex;

	const RAW: u64 = 0x55;

	#[test]
	fn normal_test_for_example() {
		let cid = "QmRZdc3mAMXpv6Akz9Ekp1y4vDSjazTx2dCQRkxVy1yUj6".parse::<Cid>().unwrap();
		let bytes = cid.encode();
		let expect = hex!("0070000000000000001200000000000000202fe65ccc17fe180c3bf4e9b8490fcc6dc74c30bf6595795dcd1136d8d9cb3f95");
		assert_eq!(bytes, expect);
		let new_cid: Cid = Decode::decode(&mut &bytes[..]).unwrap();
		assert_eq!(new_cid, cid);
	}

	macro_rules! assert_cid {
		($cid:expr, $length:expr) => {
			let mut digest = [0_u8; $length];
			digest.copy_from_slice($cid.hash().digest());
			let raw =
				($cid.version(), $cid.codec(), ($cid.hash().code(), $cid.hash().size(), digest));
			let raw_encode = Encode::encode(&raw);
			let bytes = $cid.encode();
			assert_eq!(bytes, raw_encode);
			let new_cid: Cid = Decode::decode(&mut &bytes[..]).unwrap();
			assert_eq!(new_cid, $cid);
		};
	}

	// those test case is from crate cid
	#[test]
	fn v0_handling() {
		let old = "QmdfTbBqBPQ7VNxZEYEj14VmRuZBkqFbiwReogJgS1zR1n";
		let cid = old.parse::<Cid>().unwrap();

		assert_eq!(cid.version(), Version::V0);
		assert_eq!(cid.to_string(), old);

		// for Cid v0 hash is 32 length
		assert_cid!(cid, 32);
	}

	#[test]
	fn v1_handling() {
		let expected_cid = "bafkreibme22gw2h7y2h7tg2fhqotaqjucnbc24deqo72b6mkl2egezxhvy";
		let cid: Cid = Cid::new_v1(RAW, Code::Sha2_256.digest(b"foo"));
		assert_eq!(cid.to_string_of_base(Base::Base32Lower).unwrap(), expected_cid);

		// for sha256 hash is 32 length
		assert_cid!(cid, 32);
	}

	// test case from https://github.com/ipfs/go-cid/blob/master/cid_test.go#L662
	#[test]
	fn v1_handling2() {
		let cid1 = "k2cwueckqkibutvhkr4p2ln2pjcaxaakpd9db0e7j7ax1lxhhxy3ekpv"
			.parse::<Cid>()
			.unwrap();
		let cid2 = "zb2rhZi1JR4eNc2jBGaRYJKYM8JEB4ovenym8L1CmFsRAytkz".parse::<Cid>().unwrap();
		assert_cid!(cid1, 32);
		assert_cid!(cid2, 32);
	}

	#[test]
	fn v1_handling3() {
		let cid = Cid::new_v1(RAW, Code::Sha2_512.digest(b"foo"));
		assert_cid!(cid, 64);

		let cid = Cid::new_v1(RAW, Code::Keccak384.digest(b"foo"));
		assert_cid!(cid, 48);

		let cid = Cid::new_v1(RAW, Code::Sha3_224.digest(b"foo"));
		assert_cid!(cid, 28);

		let cid = Cid::new_v1(RAW, Code::Blake2s128.digest(b"foo"));
		assert_cid!(cid, 16);
	}
}
