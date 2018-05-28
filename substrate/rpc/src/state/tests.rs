// Copyright 2017 Parity Technologies (UK) Ltd.
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
use self::error::{Error, ErrorKind};
use test_client::{self, TestClient};

#[test]
fn should_return_storage() {
	let client = Arc::new(test_client::new());
	let genesis_hash = client.genesis_hash();

	assert_matches!(
		StateApi::storage_at(&client, StorageKey(vec![10]), genesis_hash),
		Err(Error(ErrorKind::Client(client::error::ErrorKind::NoValueForKey(ref k)), _)) if *k == vec![10]
	)
}

#[test]
fn should_call_contract() {
	let client = Arc::new(test_client::new());
	let genesis_hash = client.genesis_hash();

	assert_matches!(
		StateApi::call_at(&client, "balanceOf".into(), vec![1,2,3], genesis_hash),
		Err(Error(ErrorKind::Client(client::error::ErrorKind::Execution(_)), _))
	)
}
