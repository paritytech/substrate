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

//! Rust implementation of Polkadot contracts.

use primitives::contract::{CallData, OutData};
use serializer::{from_slice as de, to_vec as ser};
use state_machine::{StaticExternalities, Externalities, CodeExecutor};

use error::{Error, ErrorKind, Result};
use auth;
use balances;
use validator_set;

/// Dummy rust executor for contracts.
///
/// Instead of actually executing the provided code it just
/// dispatches the calls to pre-defined hardcoded implementations in rust.
#[derive(Debug, Default)]
pub struct RustExecutor {
	auth: auth::Contract,
	balance: balances::Contract,
	validator_set: validator_set::Contract,
}

impl CodeExecutor for RustExecutor {
	type Error = Error;

	fn call<E: Externalities<Self>>(
		&self,
		ext: &mut E,
		code: &[u8],
		method: &str,
		data: &CallData,
	) -> Result<OutData> {
		ensure!(code.len() == 1, ErrorKind::InvalidCode(code.to_vec()));

		Ok(OutData(match method {
			"check_auth" => ser(&self.auth.check_auth(ext, de(&data.0)?)?),
			"balance_of" => ser(&self.balance.balance_of(ext, de(&data.0)?)?),
			"next_nonce" => ser(&self.balance.next_nonce(ext, de(&data.0)?)?),
			"transfer_preconditions" => ser(&self.balance.transfer_preconditions(ext, de(&data.0)?)?),
			"validator_set" => ser(&self.validator_set.validator_set(ext, de(&data.0)?)?),
			"transfer" => ser(&self.balance.transfer(ext, de(&data.0)?)?),
			m => bail!(ErrorKind::MethodNotFound(m.to_owned())),
		}))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use primitives::Address;
	use primitives::hash::H256;

	#[derive(Debug, Default)]
	struct TestExternalities;
	impl Externalities<RustExecutor> for TestExternalities {
		fn set_storage(&mut self, _key: H256, _value: Vec<u8>) {
			unimplemented!()
		}

		fn call(&mut self, _address: &Address, _method: &str, _data: &CallData) -> Result<OutData> {
			unimplemented!()
		}
	}

	impl StaticExternalities<RustExecutor> for TestExternalities {
		type Error = Error;

		fn storage(&self, _key: &H256) -> Result<&[u8]> {
			unimplemented!()
		}

		fn call_static(&self, _address: &Address, _method: &str, _data: &CallData) -> Result<OutData> {
			unimplemented!()
		}
	}

	#[test]
	fn should_fail_on_invalid_method() {
		// given
		let mut ext = TestExternalities::default();
		let executor = RustExecutor::default();

		assert_matches!(
			*executor.call(&mut ext, "any", &CallData(vec![])).unwrap_err().kind(),
			ErrorKind::MethodNotFound(ref method) if &*method == "any"
		);
	}
}
