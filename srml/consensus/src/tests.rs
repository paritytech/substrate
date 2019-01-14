// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Tests for the module.

#![cfg(test)]

use primitives::{generic, testing::{self, UintAuthorityId}, traits::{OnFinalise, ProvideInherent}};
use runtime_io::with_externalities;
use mock::{Consensus, System, new_test_ext};

#[test]
fn authorities_change_logged() {
	with_externalities(&mut new_test_ext(vec![1, 2, 3]), || {
		System::initialise(&1, &Default::default(), &Default::default());
		Consensus::set_authorities(&[UintAuthorityId(4), UintAuthorityId(5), UintAuthorityId(6)]);
		Consensus::on_finalise(1);
		let header = System::finalise();
		assert_eq!(header.digest, testing::Digest {
			logs: vec![
				generic::DigestItem::AuthoritiesChange(vec![UintAuthorityId(4).into(), UintAuthorityId(5).into(), UintAuthorityId(6).into()]),
			],
		});
	});
}

#[test]
fn authorities_change_is_not_logged_when_not_changed() {
	with_externalities(&mut new_test_ext(vec![1, 2, 3]), || {
		System::initialise(&1, &Default::default(), &Default::default());
		Consensus::on_finalise(1);
		let header = System::finalise();
		assert_eq!(header.digest, testing::Digest {
			logs: vec![],
		});
	});
}

#[test]
fn authorities_change_is_not_logged_when_changed_back_to_original() {
	with_externalities(&mut new_test_ext(vec![1, 2, 3]), || {
		System::initialise(&1, &Default::default(), &Default::default());
		Consensus::set_authorities(&[UintAuthorityId(4), UintAuthorityId(5), UintAuthorityId(6)]);
		Consensus::set_authorities(&[UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);
		Consensus::on_finalise(1);
		let header = System::finalise();
		assert_eq!(header.digest, testing::Digest {
			logs: vec![],
		});
	});
}

#[test]
fn offline_report_can_be_excluded() {
	with_externalities(&mut new_test_ext(vec![1, 2, 3]), || {
		System::initialise(&1, &Default::default(), &Default::default());
		assert!(Consensus::create_inherent_extrinsics(Vec::new()).is_empty());
		assert_eq!(Consensus::create_inherent_extrinsics(vec![0]).len(), 1);
	});
}
