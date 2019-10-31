use rstd::marker::PhantomData;
use rstd::vec::Vec;
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use codec::{Encode, Decode};
use primitives::{U256, H256, H160};
use sr_primitives::traits::UniqueSaturatedInto;
use support::storage::{StorageMap, StorageDoubleMap};
use sha3::{Keccak256, Digest};
use evm::Config;
use evm::backend::{Backend as BackendT, ApplyBackend, Apply};
use crate::{Trait, Accounts, AccountStorages, Module, Event};

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Account {
	pub nonce: U256,
	pub balance: U256,
	pub code: Vec<u8>,
}

impl Account {
	pub fn is_empty(&self) -> bool {
		self.nonce == U256::zero() && self.balance == U256::zero() &&
			self.code.len() == 0
	}
}

#[derive(Clone, Eq, PartialEq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Log {
	pub address: H160,
	pub topics: Vec<H256>,
	pub data: Vec<u8>,
}

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Vicinity {
	pub gas_price: U256,
	pub origin: H160,
}

pub static GASOMETER_CONFIG: Config = Config::istanbul();

pub struct Backend<'vicinity, T> {
	vicinity: &'vicinity Vicinity,
	_marker: PhantomData<T>,
}

impl<'vicinity, T> Backend<'vicinity, T> {
	pub fn new(vicinity: &'vicinity Vicinity) -> Self {
		Self { vicinity, _marker: PhantomData }
	}

	fn account(&self, address: H160) -> Account {
		Accounts::get(address)
	}
}

impl<'vicinity, T: Trait> BackendT for Backend<'vicinity, T> {
	fn gas_price(&self) -> U256 { self.vicinity.gas_price }
	fn origin(&self) -> H160 { self.vicinity.origin }

	fn block_hash(&self, number: U256) -> H256 {
		if number > U256::from(u32::max_value()) {
			H256::default()
		} else {
			let number = T::BlockNumber::from(number.as_u32());
			H256::from_slice(system::Module::<T>::block_hash(number).as_ref())
		}
	}

	fn block_number(&self) -> U256 {
		let number: u128 = system::Module::<T>::block_number().unique_saturated_into();
		U256::from(number)
	}

	fn block_coinbase(&self) -> H160 {
		H160::default()
	}

	fn block_timestamp(&self) -> U256 {
		let now: u128 = timestamp::Module::<T>::get().unique_saturated_into();
		U256::from(now)
	}

	fn block_difficulty(&self) -> U256 {
		U256::zero()
	}

	fn block_gas_limit(&self) -> U256 {
		U256::zero()
	}

	fn chain_id(&self) -> U256 {
		U256::one()
	}

	fn exists(&self, _address: H160) -> bool {
		true
	}

	fn basic(&self, address: H160) -> evm::backend::Basic {
		let account = self.account(address);

		evm::backend::Basic {
			balance: account.balance,
			nonce: account.nonce,
		}
	}

	fn code_size(&self, address: H160) -> usize {
		self.account(address).code.len()
	}

	fn code_hash(&self, address: H160) -> H256 {
		H256::from_slice(Keccak256::digest(&self.account(address).code).as_slice())
	}

	fn code(&self, address: H160) -> Vec<u8> {
		self.account(address).code.clone()
	}

	fn storage(&self, address: H160, index: H256) -> H256 {
		AccountStorages::get(address, index)
	}
}

impl<'vicinity, T: Trait> ApplyBackend for Backend<'vicinity, T> {
	fn apply<A, I, L>(
		&mut self,
		values: A,
		logs: L,
		delete_empty: bool,
	) where
		A: IntoIterator<Item=Apply<I>>,
		I: IntoIterator<Item=(H256, H256)>,
		L: IntoIterator<Item=evm::backend::Log>,
	{
		for apply in values {
			match apply {
				Apply::Modify {
					address, basic, code, storage, reset_storage,
				} => {
					let mut account = self.account(address);

					account.balance = basic.balance;
					account.nonce = basic.nonce;
					if let Some(code) = code {
						account.code = code;
					}

					if reset_storage {
						AccountStorages::remove_prefix(address);
					}

					for (index, value) in storage {
						if value == H256::default() {
							AccountStorages::remove(address, index);
						} else {
							AccountStorages::insert(address, index, value);
						}
					}

					if delete_empty && account.is_empty() {
						Accounts::remove(address);
					} else {
						Accounts::insert(address, account);
					}
				},
				Apply::Delete { address } => {
					Accounts::remove(address);
				},
			}
		}

		for log in logs {
			Module::<T>::deposit_event(Event::Log(Log {
				address: log.address,
				topics: log.topics,
				data: log.data,
			}));
		}
	}
}
