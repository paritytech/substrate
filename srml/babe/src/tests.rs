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
#![allow(unused_imports)]
#![cfg(test)]
use super::*;
use runtime_io::with_externalities;
use mock::{new_test_ext, Babe, Test};
use sr_primitives::{traits::Header, Digest};
use babe_primitives::CompatibleDigestItem;
use session::ShouldEndSession;

#[test]
fn empty_randomness_is_correct() {
	let s = compute_randomness([0; RANDOMNESS_LENGTH], 0, std::iter::empty(), None);
	assert_eq!(s, [74, 25, 49, 128, 53, 97, 244, 49, 222, 202, 176, 2, 231, 66, 95, 10, 133, 49, 213, 228, 86, 161, 164, 127, 217, 153, 138, 37, 48, 192, 248, 0]);
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
fn check_epoch_change() {
	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		System::initialize(&1, &Default::default(), &Default::default(), &Default::default());
		assert!(!Babe::should_end_session(0), "Genesis does not change sessions");
		assert!(!Babe::should_end_session(200000),
			"BABE does not include the block number in epoch calculations");
		let header = System::finalize();
		assert_eq!(header.digest, Digest { logs: vec![] });
		System::initialize(&3, &header.hash(), &Default::default(), &Default::default());
		EpochStartSlot::put(1);
		CurrentSlot::put(3);
		let header = System::finalize();
		assert_eq!(header.digest, Digest { logs: vec![] });
		assert!(!Babe::should_end_session(0));
		System::initialize(&4, &header.hash(), &Default::default(), &Default::default());
		CurrentSlot::put(4);
		assert!(Babe::should_end_session(0));
		Babe::randomness_change_epoch(1);
		let header = System::finalize();
		let Digest { ref logs } = header.digest;
		assert_eq!(logs.len(), 1);
		let (engine_id, mut epoch) = logs[0].as_consensus().unwrap();
		assert_eq!(BABE_ENGINE_ID, engine_id);
		let Epoch { start_slot, duration, .. } = match ConsensusLog::decode(&mut epoch).unwrap() {
			ConsensusLog::NextEpochData(e) => e,
			ConsensusLog::OnDisabled(_) => panic!("we have not disabled any authorities yet!"),
		};
		assert_eq!(EpochDuration::get(), 3);
		assert_eq!(duration, EpochDuration::get());
		assert_eq!(start_slot, 2 * EpochDuration::get() + 1);
	})
}

#[test]
fn authority_index() {
	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		assert_eq!(Babe::find_author((&[(BABE_ENGINE_ID, &[][..])]).into_iter().cloned()), None,
			"Trivially invalid authorities are ignored");
		assert_eq!(Babe::find_author((&[(BABE_ENGINE_ID, &[][..])]).into_iter().cloned()), None,
			"Trivially invalid authorities are ignored")
	})
}
