// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Tests for the module.

#![cfg(test)]

use codec::Decode;
use primitives::{BuildStorage, testing::{Digest, Header}};
use substrate_primitives::H256;
use runtime_io::{PREFIX_KEY, TestExternalities, PurgeFilterResult,
	storage, clear_storage, purge_storage, with_externalities};
use super::*;

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct Test;

impl Trait for Test {
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = ::primitives::traits::BlakeTwo256;
	type Digest = Digest;
	type AccountId = u64;
	type Header = Header;
}

fn new_test_ext(use_prefix: bool) -> TestExternalities {
	let mut ext = if use_prefix {
		GenesisConfig::<Test> {
			use_block_number_prefix: use_prefix,
			storage_purge_interval: if use_prefix { Some(4) } else { None },
			min_purged_value_age: if use_prefix { Some(2) } else { None },
		}
	} else {
		Default::default()
	}.build_storage().unwrap();
	ext.insert(b"dog".to_vec(), b"good".to_vec());
	ext
}

#[test]
fn initialise_does_not_set_storage_prefix_by_default() {
	with_externalities(&mut new_test_ext(false), || {
		Module::<Test>::initialise(&1, &Default::default(), &Default::default());
		assert!(storage(PREFIX_KEY).is_none());
	});
}

#[test]
fn initialise_sets_storage_prefix_when_configured() {
	with_externalities(&mut new_test_ext(true), || {
		Module::<Test>::initialise(&1, &Default::default(), &Default::default());
		assert_eq!(Some(1u64), storage(PREFIX_KEY).and_then(|p| Decode::decode(&mut &p[..])));
	});
}

#[test]
fn key_is_not_scheduled_for_purge_if_created_and_deleted_in_the_same_block() {
	with_externalities(&mut new_test_ext(true), || {
		clear_storage(b"cat");
		assert_eq!(purge_storage(|_, _, _| PurgeFilterResult::Purge), 0);
	});
}

#[test]
fn key_is_scheduled_for_purge() {
	with_externalities(&mut new_test_ext(true), || {
		clear_storage(b"dog");
		assert_eq!(purge_storage(|_, _, _| PurgeFilterResult::Purge), 1);
	});
}
