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

use primitives::contract::CallData;
use primitives::uint::U256;
use primitives::{hash, Address};
use serializer;
use state_machine::{self, Externalities, StaticExternalities};

use error::{Error, ErrorKind, Result, ResultExt};
use executor::RustExecutor;

/// Account entry
#[derive(Default, Debug, Serialize, Deserialize)]
struct Account {
	/// Account balance
	balance: U256,
	/// Account nonce
	nonce: U256,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transfer {
	/// Transfer value
	value: U256,
	/// Transfer destination
	to: Address,
	/// Replay protection
	nonce: U256,
	/// Data authorizing the transfer (we can derive sender from it)
	authentication_data: Vec<u8>,
}

fn externalities_error<E: state_machine::Error>(e: E) -> Error {
	ErrorKind::Externalities(Box::new(e)).into()
}
fn address(x: u8) -> Address {
	[x].as_ref().into()
}

/// Balances contract rust implementation.
#[derive(Debug, Default)]
pub struct Contract;
impl Contract {
	fn account<E: StaticExternalities<RustExecutor>>(ext: &E, address: Address) -> Result<Account> {
		ext.storage(&address.into())
			.map_err(externalities_error)
			.and_then(|x| if x.is_empty() {
				Ok(Account::default())
			} else {
				serializer::from_slice(x).chain_err(|| "Invalid internal structure.")
			})
	}

	fn contains_sender(sender: Address, addresses: &[Address]) -> bool {
		addresses.iter().find(|address| *address == &sender).is_some()
	}

	/// Returns a balance of given address.
	pub fn balance_of<E: StaticExternalities<RustExecutor>>(&self, ext: &E, data: Address) -> Result<U256> {
		Self::account(ext, data).map(|acc| acc.balance)
	}

	/// Returns the next nonce to authorize the transfer from given address.
	pub fn next_nonce<E: StaticExternalities<RustExecutor>>(&self, ext: &E, data: Address) -> Result<U256> {
		Self::account(ext, data).map(|acc| acc.nonce)
	}

	/// Checks preconditions for transfer.
	/// Should verify:
	/// - signature
	/// - replay protection
	/// - enough balance
	pub fn transfer_preconditions<E: StaticExternalities<RustExecutor>>(&self, ext: &E, data: Transfer) -> Result<Option<Address>> {
		// Check the caller:
		let sender = ext.sender();
		if !Self::contains_sender(*sender, &[
			address(RustExecutor::TOP_LEVEL),
			address(RustExecutor::BALANCES),
		]) {
			return Ok(None)
		}

		// check signature
		let mut bytes = [0u8; 32 + 20 + 32];
		data.value.to_big_endian(&mut bytes[0..32]);
		bytes[32..52].clone_from_slice(&*data.to);
		data.nonce.to_big_endian(&mut bytes[52..84]);
		let hash = hash(&bytes);

		let sender = serializer::from_slice(&ext.call_static(
			&address(RustExecutor::TOP_LEVEL),
			"check_auth",
			&CallData(serializer::to_vec(&(hash, data.authentication_data))),
		).map_err(externalities_error)?.0)
			.chain_err(|| "Invalid auth contract response.")?;

		let account = Self::account(ext, sender)?;

		// check nonce
		if account.nonce != data.nonce {
			return Ok(None)
		}

		// check balance
		if account.balance < data.value {
			return Ok(None)
		}

		// return sender and account
		Ok(Some(sender))
	}

	/// Perform a transfer.
	/// This should first make sure that precondtions are satisfied and later perform the transfer.
	pub fn transfer<E: Externalities<RustExecutor>>(&self, ext: &mut E, data: Transfer) -> Result<bool> {
		let from = match self.transfer_preconditions(ext, data.clone())? {
			None => return Ok(false),
			Some(address) => address,
		};

		let mut sender = Self::account(ext, from)?;
		let mut recipient = Self::account(ext, data.to)?;

		// update nonce
		sender.nonce = sender.nonce.checked_add(&1.into())
			.ok_or_else(|| ErrorKind::OperationOverflow)?;

		// update balances
		sender.balance = sender.balance.checked_sub(&data.value)
			.ok_or_else(|| ErrorKind::OperationOverflow)?;
		recipient.balance = recipient.balance.checked_add(&data.value)
			.ok_or_else(|| ErrorKind::OperationOverflow)?;

		// save changes to the storage
		ext.set_storage(data.to.into(), serializer::to_vec(&recipient));
		ext.set_storage(from.into(), serializer::to_vec(&sender));

		Ok(true)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use test_helpers::TestExternalities;

	#[test]
	fn should_return_balance_of_and_do_a_transfer() {
		// given
		let mut ext = TestExternalities::default();
		ext.call_result = Some(serializer::to_vec(&Address::from(5)));
		ext.storage.insert(5.into(), serializer::to_vec(&Account {
			nonce: 0.into(),
			balance: 10.into(),
		}));

		let balances = Contract::default();
		let transfer = Transfer {
			value: 5.into(),
			to: 1.into(),
			nonce: 0.into(),
			authentication_data: vec![5],
		};
		assert_eq!(balances.balance_of(&ext, 5.into()).unwrap(), 10.into());
		assert_eq!(balances.balance_of(&ext, 1.into()).unwrap(), 0.into());
		assert_eq!(balances.next_nonce(&ext, 5.into()).unwrap(), 0.into());

		// when
		assert!(balances.transfer_preconditions(&ext, transfer.clone()).unwrap().is_some());
		assert_eq!(balances.transfer(&mut ext, transfer).unwrap(), true);

		// then
		assert_eq!(balances.balance_of(&ext, 5.into()).unwrap(), 5.into());
		assert_eq!(balances.balance_of(&ext, 1.into()).unwrap(), 5.into());
		assert_eq!(balances.next_nonce(&ext, 5.into()).unwrap(), 1.into());
	}

	#[test]
	fn should_reject_on_invalid_nonce() {
		// given
		let mut ext = TestExternalities::default();
		ext.call_result = Some(serializer::to_vec(&Address::from(5)));
		ext.storage.insert(5.into(), serializer::to_vec(&Account {
			nonce: 0.into(),
			balance: 10.into(),
		}));

		let balances = Contract::default();
		let transfer = Transfer {
			value: 5.into(),
			to: 1.into(),
			nonce: 1.into(),
			authentication_data: vec![5],
		};

		assert!(balances.transfer_preconditions(&ext, transfer.clone()).unwrap().is_none());
	}

	#[test]
	fn should_reject_on_insufficient_balance() {
		// given
		let mut ext = TestExternalities::default();
		ext.call_result = Some(serializer::to_vec(&Address::from(5)));
		ext.storage.insert(5.into(), serializer::to_vec(&Account {
			nonce: 0.into(),
			balance: 4.into(),
		}));

		let balances = Contract::default();
		let transfer = Transfer {
			value: 5.into(),
			to: 1.into(),
			nonce: 0.into(),
			authentication_data: vec![5],
		};

		assert!(balances.transfer_preconditions(&ext, transfer.clone()).unwrap().is_none());
	}

	#[test]
	fn should_reject_on_non_top_level_call() {
		// given
		let mut ext = TestExternalities::default();
		ext.sender = 1.into();
		ext.call_result = Some(serializer::to_vec(&Address::from(5)));
		ext.storage.insert(5.into(), serializer::to_vec(&Account {
			nonce: 0.into(),
			balance: 10.into(),
		}));

		let balances = Contract::default();
		let transfer = Transfer {
			value: 5.into(),
			to: 1.into(),
			nonce: 0.into(),
			authentication_data: vec![5],
		};

		assert!(balances.transfer_preconditions(&ext, transfer.clone()).unwrap().is_none());
	}
}
