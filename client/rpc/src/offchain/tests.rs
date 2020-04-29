// Copyright 2020 Parity Technologies (UK) Ltd.
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

use super::*;
use assert_matches::assert_matches;
use sp_core::{Bytes, offchain::storage::InMemOffchainStorage};

#[test]
fn local_storage_should_work() {
	let storage = InMemOffchainStorage::default();
	let offchain = Offchain::new(storage, DenyUnsafe::No);
	let key = Bytes(b"offchain_storage".to_vec());
	let value = Bytes(b"offchain_value".to_vec());

	assert_matches!(
		offchain.set_local_storage(StorageKind::PERSISTENT, key.clone(), value.clone()),
		Ok(())
	);
	assert_matches!(
		offchain.get_local_storage(StorageKind::PERSISTENT, key),
		Ok(Some(ref v)) if *v == value
	);
}

#[test]
fn offchain_calls_considered_unsafe() {
	let storage = InMemOffchainStorage::default();
	let offchain = Offchain::new(storage, DenyUnsafe::Yes);
	let key = Bytes(b"offchain_storage".to_vec());
	let value = Bytes(b"offchain_value".to_vec());

	assert_matches!(
		offchain.set_local_storage(StorageKind::PERSISTENT, key.clone(), value.clone()),
		Err(Error::UnsafeRpcCalled(_))
	);
	assert_matches!(
		offchain.get_local_storage(StorageKind::PERSISTENT, key),
		Err(Error::UnsafeRpcCalled(_))
	);
}
