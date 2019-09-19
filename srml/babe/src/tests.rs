// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Consensus extension module tests for BABE consensus.

use super::*;
use runtime_io::with_externalities;
use mock::{new_test_ext, Babe, Test};
use sr_primitives::{traits::OnFinalize, testing::{Digest, DigestItem}};
use session::ShouldEndSession;

const EMPTY_RANDOMNESS: [u8; 32] = [
	74, 25, 49, 128, 53, 97, 244, 49,
	222, 202, 176, 2, 231, 66, 95, 10,
	133, 49, 213, 228, 86, 161, 164, 127,
	217, 153, 138, 37, 48, 192, 248, 0,
];

fn make_pre_digest(
	authority_index: babe_primitives::AuthorityIndex,
	slot_number: babe_primitives::SlotNumber,
	vrf_output: [u8; babe_primitives::VRF_OUTPUT_LENGTH],
	vrf_proof: [u8; babe_primitives::VRF_PROOF_LENGTH],
) -> Digest {
	let digest_data = babe_primitives::RawBabePreDigest::Primary {
		authority_index,
		slot_number,
		vrf_output,
		vrf_proof,
	};
	let log = DigestItem::PreRuntime(babe_primitives::BABE_ENGINE_ID, digest_data.encode());
	Digest { logs: vec![log] }
}

#[test]
fn empty_randomness_is_correct() {
	let s = compute_randomness([0; RANDOMNESS_LENGTH], 0, std::iter::empty(), None);
	assert_eq!(s, EMPTY_RANDOMNESS);
}

#[test]
fn initial_values() {
	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		assert_eq!(Babe::authorities().len(), 4)
	})
}

#[test]
fn check_module() {
	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		assert!(!Babe::should_end_session(0), "Genesis does not change sessions");
		assert!(!Babe::should_end_session(200000),
			"BABE does not include the block number in epoch calculations");
	})
}

type System = system::Module<Test>;
type Session = session::Module<Test>;
type EpochDuration = <Test as super::Trait>::EpochDuration;

#[test]
fn first_block_epoch_zero_start() {
	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		let genesis_slot = 100;
		let first_vrf = [1; 32];
		let pre_digest = make_pre_digest(
			0,
			genesis_slot,
			first_vrf,
			[0xff; 64],
		);

		assert_eq!(Babe::genesis_slot(), 0);
		System::initialize(&1, &Default::default(), &Default::default(), &pre_digest);

		// see implementation of the function for details why: we issue an
		// epoch-change digest but don't do it via the normal session mechanism.
		assert!(!Babe::should_end_session(1));
		assert_eq!(Babe::genesis_slot(), genesis_slot);
		assert_eq!(Babe::current_slot(), genesis_slot);
		assert_eq!(Babe::epoch_index(), 0);

		Babe::on_finalize(1);
		let header = System::finalize();

		assert_eq!(SegmentIndex::get(), 0);
		assert_eq!(UnderConstruction::get(0), vec![first_vrf]);
		assert_eq!(Babe::randomness(), [0; 32]);
		assert_eq!(NextRandomness::get(), [0; 32]);

		assert_eq!(header.digest.logs.len(), 2);
		assert_eq!(header.digest.logs[0], pre_digest.logs[0]);

		let authorities = Babe::authorities();
		let consensus_log = babe_primitives::ConsensusLog::NextEpochData(
			babe_primitives::NextEpochDescriptor {
				authorities,
				randomness: Babe::randomness(),
			}
		);
		let consensus_digest = DigestItem::Consensus(BABE_ENGINE_ID, consensus_log.encode());

		// first epoch descriptor has same info as last.
		assert_eq!(header.digest.logs[1], consensus_digest.clone())
	})
}

#[test]
fn authority_index() {
	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		assert_eq!(
			Babe::find_author((&[(BABE_ENGINE_ID, &[][..])]).into_iter().cloned()), None,
			"Trivially invalid authorities are ignored")
	})
}
