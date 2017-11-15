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

use std::fmt;
use std::result::Result as StdResult;
use std::collections::HashMap;

use primitives::Address;
use primitives::hash::H256;
use primitives::contract::{CallData, OutData};
use state_machine;

use executor::RustExecutor;

#[derive(Debug)]
pub enum Error {
	NoOutData
}

impl fmt::Display for Error {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Error::NoOutData => write!(fmt, "No output data"),
		}
	}
}

#[derive(Debug, Default)]
pub struct TestExternalities {
	pub sender: Address,
	pub storage: HashMap<H256, Vec<u8>>,
	pub call_result: Option<Vec<u8>>,
}

impl state_machine::StaticExternalities<RustExecutor> for TestExternalities {
	type Error = Error;

	fn sender(&self) -> &Address {
		&self.sender
	}

	fn storage(&self, key: &H256) -> StdResult<&[u8], Self::Error> {
		Ok(self.storage.get(key).map(|x| &**x).unwrap_or(&[]))
	}

	fn call_static(&self, _address: &Address, _method: &str, _data: &CallData) -> StdResult<OutData, Self::Error> {
		self.call_result.clone()
			.map(OutData)
			.ok_or(Error::NoOutData)
	}
}

impl state_machine::Externalities<RustExecutor> for TestExternalities {
	fn set_storage(&mut self, key: H256, value: Vec<u8>) {
		self.storage.insert(key, value);
	}

	fn call(&mut self, _address: &Address, _method: &str, _data: &CallData) -> StdResult<OutData, Self::Error> {
		self.call_result.take().map(OutData).ok_or(Error::NoOutData)
	}
}

