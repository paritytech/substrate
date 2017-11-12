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
use state_machine::{Externalities, Executor};

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

impl RustExecutor {
	const AUTH: u8 = 1;
	const BALANCES: u8 = 2;
	const VALIDATOR_SET: u8 = 3;
}

impl Executor for RustExecutor {
	type Error = Error;

	fn static_call<E: Externalities<Self>>(
		&self,
		ext: &E,
		code: &[u8],
		method: &str,
		data: &CallData,
	) -> Result<OutData> {
		ensure!(code.len() == 1, ErrorKind::InvalidCode(code.to_vec()));

		Ok(OutData(match code[0] {
			Self::AUTH => match method {
				"check_auth" => ser(&self.auth.check_auth(ext, de(&data.0)?)?),
				m => bail!(ErrorKind::MethodNotFound(m.to_owned())),
			},
			Self::BALANCES => match method {
				"balance_of" => ser(&self.balance.balance_of(ext, de(&data.0)?)?),
				"next_nonce" => ser(&self.balance.next_nonce(ext, de(&data.0)?)?),
				"transfer_preconditions" => ser(&self.balance.transfer_preconditions(ext, de(&data.0)?)?),
				m => bail!(ErrorKind::MethodNotFound(m.to_owned())),
			},
			Self::VALIDATOR_SET => match method {
				"validator_set" => ser(&self.validator_set.validator_set(ext, de(&data.0)?)?),
				m => bail!(ErrorKind::MethodNotFound(m.to_owned())),
			},
			c => bail!(ErrorKind::InvalidCode(vec![c])),
		}))
	}

	fn call<E: Externalities<Self>>(
		&self,
		ext: &mut E,
		code: &[u8],
		method: &str,
		data: &CallData,
	) -> Result<OutData> {
		ensure!(code.len() == 1, ErrorKind::InvalidCode(code.to_vec()));

		Ok(OutData(match code[0] {
			Self::BALANCES=> match method {
				"transfer" => ser(&self.balance.transfer(ext, de(&data.0)?)?),
				m => bail!(ErrorKind::MethodNotFound(m.to_owned())),
			},
			c => bail!(ErrorKind::InvalidCode(vec![c])),
		}))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[derive(Debug, Default)]
	struct TestExternalities;
	impl Externalities<RustExecutor> for TestExternalities {
		type Error = Error;
	}

	#[test]
	fn should_fail_for_empty_or_unknown_code() {
		// given
		let mut ext = TestExternalities::default();
		let executor = RustExecutor::default();

		assert_matches!(
			*executor.call(&mut ext, &[], "any", &CallData(vec![])).unwrap_err().kind(),
			ErrorKind::InvalidCode(ref code) if code.is_empty()
		);
		assert_matches!(
			*executor.call(&mut ext, &[1, 2], "any", &CallData(vec![])).unwrap_err().kind(),
			ErrorKind::InvalidCode(ref code) if code.len() == 2
		);
		assert_matches!(
			*executor.call(&mut ext, &[255,], "any", &CallData(vec![])).unwrap_err().kind(),
			ErrorKind::InvalidCode(_)
		);
	}

	#[test]
	fn should_fail_on_invalid_method() {
		// given
		let mut ext = TestExternalities::default();
		let executor = RustExecutor::default();

		assert_matches!(
			*executor.call(&mut ext, &[2], "any", &CallData(vec![])).unwrap_err().kind(),
			ErrorKind::MethodNotFound(ref method) if &*method == "any"
		);
	}
}
