// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! The tests for functionality concerning the metadata.

use super::*;

#[test]
fn set_external_metadata_works() {
	new_test_ext().execute_with(|| {
		use frame_support::traits::Hash as PreimageHash;
		// invalid preimage hash.
		let invalid_hash: PreimageHash = [1u8; 32].into();
		// metadata owner is an external proposal.
		let owner = MetadataOwner::External;
		// fails to set metadata if an external proposal does not exist.
		assert_noop!(
			Democracy::set_metadata(RuntimeOrigin::signed(2), owner.clone(), Some(invalid_hash)),
			Error::<Test>::NoProposal,
		);
		// create an external proposal.
		assert_ok!(Democracy::external_propose(RuntimeOrigin::signed(2), set_balance_proposal(2)));
		assert!(<NextExternal<Test>>::exists());
		// fails to set metadata with non external origin.
		assert_noop!(
			Democracy::set_metadata(RuntimeOrigin::signed(1), owner.clone(), Some(invalid_hash)),
			BadOrigin,
		);
		// fails to set non-existing preimage.
		assert_noop!(
			Democracy::set_metadata(RuntimeOrigin::signed(2), owner.clone(), Some(invalid_hash)),
			Error::<Test>::PreimageNotExist,
		);
		// set metadata successful.
		let hash = note_preimage(1);
		assert_ok!(Democracy::set_metadata(RuntimeOrigin::signed(2), owner.clone(), Some(hash)));
		System::assert_last_event(RuntimeEvent::Democracy(crate::Event::MetadataSet {
			owner,
			hash,
		}));
	});
}

#[test]
fn clear_metadata_works() {
	new_test_ext().execute_with(|| {
		// metadata owner is an external proposal.
		let owner = MetadataOwner::External;
		// create an external proposal.
		assert_ok!(Democracy::external_propose(RuntimeOrigin::signed(2), set_balance_proposal(2)));
		assert!(<NextExternal<Test>>::exists());
		// set metadata.
		let hash = note_preimage(1);
		assert_ok!(Democracy::set_metadata(RuntimeOrigin::signed(2), owner.clone(), Some(hash)));
		// fails to clear metadata with a wrong origin.
		assert_noop!(
			Democracy::set_metadata(RuntimeOrigin::signed(1), owner.clone(), None),
			BadOrigin,
		);
		// clear metadata successful.
		assert_ok!(Democracy::set_metadata(RuntimeOrigin::signed(2), owner.clone(), None));
		System::assert_last_event(RuntimeEvent::Democracy(crate::Event::MetadataCleared {
			owner,
			hash,
		}));
	});
}

#[test]
fn set_proposal_metadata_works() {
	new_test_ext().execute_with(|| {
		use frame_support::traits::Hash as PreimageHash;
		// invalid preimage hash.
		let invalid_hash: PreimageHash = [1u8; 32].into();
		// create an external proposal.
		assert_ok!(propose_set_balance(1, 2, 5));
		// metadata owner is a public proposal.
		let owner = MetadataOwner::Proposal(Democracy::public_prop_count() - 1);
		// fails to set non-existing preimage.
		assert_noop!(
			Democracy::set_metadata(RuntimeOrigin::signed(1), owner.clone(), Some(invalid_hash)),
			Error::<Test>::PreimageNotExist,
		);
		// note preimage.
		let hash = note_preimage(1);
		// fails to set a preimage if an origin is not a proposer.
		assert_noop!(
			Democracy::set_metadata(RuntimeOrigin::signed(3), owner.clone(), Some(hash)),
			Error::<Test>::NoPermission,
		);
		// set metadata successful.
		assert_ok!(Democracy::set_metadata(RuntimeOrigin::signed(1), owner.clone(), Some(hash)));
		System::assert_last_event(RuntimeEvent::Democracy(crate::Event::MetadataSet {
			owner,
			hash,
		}));
	});
}

#[test]
fn clear_proposal_metadata_works() {
	new_test_ext().execute_with(|| {
		// create an external proposal.
		assert_ok!(propose_set_balance(1, 2, 5));
		// metadata owner is a public proposal.
		let owner = MetadataOwner::Proposal(Democracy::public_prop_count() - 1);
		// set metadata.
		let hash = note_preimage(1);
		assert_ok!(Democracy::set_metadata(RuntimeOrigin::signed(1), owner.clone(), Some(hash)));
		// fails to clear metadata with a wrong origin.
		assert_noop!(
			Democracy::set_metadata(RuntimeOrigin::signed(3), owner.clone(), None),
			Error::<Test>::NoPermission,
		);
		// clear metadata successful.
		assert_ok!(Democracy::set_metadata(RuntimeOrigin::signed(1), owner.clone(), None));
		System::assert_last_event(RuntimeEvent::Democracy(crate::Event::MetadataCleared {
			owner,
			hash,
		}));
	});
}

#[test]
fn set_referendum_metadata_by_root() {
	new_test_ext().execute_with(|| {
		let index = Democracy::inject_referendum(
			2,
			set_balance_proposal(2),
			VoteThreshold::SuperMajorityApprove,
			0,
		);
		// metadata owner is a referendum.
		let owner = MetadataOwner::Referendum(index);
		// note preimage.
		let hash = note_preimage(1);
		// fails to set if not a root.
		assert_noop!(
			Democracy::set_metadata(RuntimeOrigin::signed(3), owner.clone(), Some(hash)),
			Error::<Test>::NoPermission,
		);
		// fails to clear if not a root.
		assert_noop!(
			Democracy::set_metadata(RuntimeOrigin::signed(3), owner.clone(), None),
			Error::<Test>::NoPermission,
		);
		// succeed to set metadata by a root for an ongoing referendum.
		assert_ok!(Democracy::set_metadata(RuntimeOrigin::root(), owner.clone(), Some(hash)));
		System::assert_last_event(RuntimeEvent::Democracy(crate::Event::MetadataSet {
			owner: owner.clone(),
			hash,
		}));
		// succeed to clear metadata by a root for an ongoing referendum.
		assert_ok!(Democracy::set_metadata(RuntimeOrigin::root(), owner.clone(), None));
		System::assert_last_event(RuntimeEvent::Democracy(crate::Event::MetadataCleared {
			owner,
			hash,
		}));
	});
}

#[test]
fn clear_referendum_metadata_works() {
	new_test_ext().execute_with(|| {
		// create a referendum.
		let index = Democracy::inject_referendum(
			2,
			set_balance_proposal(2),
			VoteThreshold::SuperMajorityApprove,
			0,
		);
		// metadata owner is a referendum.
		let owner = MetadataOwner::Referendum(index);
		// set metadata.
		let hash = note_preimage(1);
		// referendum finished.
		MetadataOf::<Test>::insert(owner.clone(), hash);
		// no permission to clear metadata of an ongoing referendum.
		assert_noop!(
			Democracy::set_metadata(RuntimeOrigin::signed(1), owner.clone(), None),
			Error::<Test>::NoPermission,
		);
		// referendum finished.
		ReferendumInfoOf::<Test>::insert(
			index,
			ReferendumInfo::Finished { end: 1, approved: true },
		);
		// clear metadata successful.
		assert_ok!(Democracy::set_metadata(RuntimeOrigin::signed(1), owner.clone(), None));
		System::assert_last_event(RuntimeEvent::Democracy(crate::Event::MetadataCleared {
			owner,
			hash,
		}));
	});
}
