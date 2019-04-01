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

//! Tests for the module.

#![cfg(test)]

use primitives::{generic, testing::{self, UintAuthorityId}, traits::OnFinalize};
use runtime_io::with_externalities;
use crate::mock::{Consensus, System, new_test_ext};
use inherents::{InherentData, ProvideInherent};

#[test]
fn authorities_change_logged() {
	with_externalities(&mut new_test_ext(vec![1, 2, 3]), || {
		System::initialize(&1, &Default::default(), &Default::default());
		Consensus::set_authorities(&[UintAuthorityId(4), UintAuthorityId(5), UintAuthorityId(6)]);
		Consensus::on_finalize(1);
		let header = System::finalize();
		assert_eq!(header.digest, testing::Digest {
			logs: vec![
				generic::DigestItem::AuthoritiesChange(
					vec![
						UintAuthorityId(4).into(),
						UintAuthorityId(5).into(),
						UintAuthorityId(6).into()
					]
				),
			],
		});
	});
}

#[test]
fn partial_authorities_change_logged() {
	with_externalities(&mut new_test_ext(vec![1, 2, 3]), || {
		System::initialize(&2, &Default::default(), &Default::default());
		Consensus::set_authorities(&[UintAuthorityId(2), UintAuthorityId(4), UintAuthorityId(5)]);
		Consensus::on_finalize(2);
		let header = System::finalize();
		assert_eq!(header.digest, testing::Digest {
			logs: vec![
				generic::DigestItem::AuthoritiesChange(
					vec![
						UintAuthorityId(2).into(),
						UintAuthorityId(4).into(),
						UintAuthorityId(5).into()
					]
				),
			],
		});
	});
}

#[test]
fn authorities_change_is_not_logged_when_not_changed() {
	with_externalities(&mut new_test_ext(vec![1, 2, 3]), || {
		System::initialize(&1, &Default::default(), &Default::default());
		Consensus::on_finalize(1);
		let header = System::finalize();
		assert_eq!(header.digest, testing::Digest {
			logs: vec![],
		});
	});
}

#[test]
fn authorities_change_is_not_logged_when_changed_back_to_original() {
	with_externalities(&mut new_test_ext(vec![1, 2, 3]), || {
		System::initialize(&1, &Default::default(), &Default::default());
		Consensus::set_authorities(&[UintAuthorityId(4), UintAuthorityId(5), UintAuthorityId(6)]);
		Consensus::set_authorities(&[UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);
		Consensus::on_finalize(1);
		let header = System::finalize();
		assert_eq!(header.digest, testing::Digest {
			logs: vec![],
		});
	});
}

#[test]
fn offline_report_can_be_excluded() {
	with_externalities(&mut new_test_ext(vec![1, 2, 3]), || {
		System::initialize(&1, &Default::default(), &Default::default());
		assert!(Consensus::create_inherent(&InherentData::new()).is_none());

		let offline_report: Vec<u32> = vec![0];
		let mut data = InherentData::new();
		data.put_data(super::INHERENT_IDENTIFIER, &offline_report).unwrap();

		assert!(Consensus::create_inherent(&data).is_some());
	});
}

#[test]
fn set_and_kill_storage_work() {
	use srml_support::storage;

	with_externalities(&mut new_test_ext(vec![1, 2, 3]), || {
		System::initialize(&1, &Default::default(), &Default::default());

		let item = (vec![42u8], vec![42u8]);

		Consensus::set_storage(vec![item.clone()]).unwrap();

		assert_eq!(
			storage::unhashed::get_raw(&item.0),
			Some(item.1),
		);

		Consensus::kill_storage(vec![item.0.clone()]).unwrap();

		assert_eq!(
			storage::unhashed::get_raw(&item.0),
			None,
		);
	});
}
