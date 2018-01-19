// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

use super::*;
use polkadot_executor as executor;

use self::error::{Error, ErrorKind};
use test_helpers::Blockchain;

#[test]
fn should_return_storage() {
	let client = Client::new(Blockchain::default(), executor::executor());

	assert_matches!(
		StateApi::storage(&client, StorageKey(vec![10]), 0.into()),
		Ok(ref x) if x.0.is_empty()
	)
}

#[test]
#[ignore]	// TODO: [ToDr] reenable once we can properly mock the wasm executor env
fn should_call_contract() {
	// TODO [ToDr] Fix test after we are able to mock state.
	let client = Client::new(Blockchain::default(), executor::executor());

	assert_matches!(
		StateApi::call(&client, "balanceOf".into(), CallData(vec![1,2,3]), 0.into()),
		Err(Error(ErrorKind::Client(client::error::ErrorKind::Execution(_)), _))
	)
}
