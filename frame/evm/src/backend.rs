use sp_std::marker::PhantomData;
use sp_std::vec::Vec;
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use codec::{Encode, Decode};
use sp_core::{U256, H256, H160};
use sp_runtime::traits::UniqueSaturatedInto;
use frame_support::storage::{StorageMap, StorageDoubleMap};
use sha3::{Keccak256, Digest};
use evm::Config;
use evm::backend::{Backend as BackendT, ApplyBackend, Apply};
use crate::{Trait, Accounts, AccountStorages, AccountCodes, Module, Event};

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
/// Ethereum account nonce, balance and code. Used by storage.
pub struct Account {
	/// Account nonce.
	pub nonce: U256,
	/// Account balance.
	pub balance: U256,
}

#[derive(Clone, Eq, PartialEq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
/// Ethereum log. Used for `deposit_event`.
pub struct Log {
	/// Source address of the log.
	pub address: H160,
	/// Topics of the log.
	pub topics: Vec<H256>,
	/// Byte array data of the log.
	pub data: Vec<u8>,
}

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
/// External input from the transaction.
pub struct Vicinity {
	/// Current transaction gas price.
	pub gas_price: U256,
	/// Origin of the transaction.
	pub origin: H160,
}

/// Gasometer config used for executor. Currently this is hard-coded to
/// Istanbul hard fork.
pub static GASOMETER_CONFIG: Config = Config::istanbul();

/// Substrate backend for EVM.
pub struct Backend<'vicinity, T> {
	vicinity: &'vicinity Vicinity,
	_marker: PhantomData<T>,
}

impl<'vicinity, T> Backend<'vicinity, T> {
	/// Create a new backend with given vicinity.
	pub fn new(vicinity: &'vicinity Vicinity) -> Self {
		Self { vicinity, _marker: PhantomData }
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
			H256::from_slice(frame_system::Module::<T>::block_hash(number).as_ref())
		}
	}

	fn block_number(&self) -> U256 {
		let number: u128 = frame_system::Module::<T>::block_number().unique_saturated_into();
		U256::from(number)
	}

	fn block_coinbase(&self) -> H160 {
		H160::default()
	}

	fn block_timestamp(&self) -> U256 {
		let now: u128 = pallet_timestamp::Module::<T>::get().unique_saturated_into();
		U256::from(now)
	}

	fn block_difficulty(&self) -> U256 {
		U256::zero()
	}

	fn block_gas_limit(&self) -> U256 {
		U256::zero()
	}

	fn chain_id(&self) -> U256 {
		U256::from(sp_io::misc::chain_id())
	}

	fn exists(&self, _address: H160) -> bool {
		true
	}

	fn basic(&self, address: H160) -> evm::backend::Basic {
		let account = Accounts::get(&address);

		evm::backend::Basic {
			balance: account.balance,
			nonce: account.nonce,
		}
	}

	fn code_size(&self, address: H160) -> usize {
		AccountCodes::decode_len(&address).unwrap_or(0)
	}

	fn code_hash(&self, address: H160) -> H256 {
		H256::from_slice(Keccak256::digest(&AccountCodes::get(&address)).as_slice())
	}

	fn code(&self, address: H160) -> Vec<u8> {
		AccountCodes::get(&address)
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
		#[cfg(feature = "storage_tracing")] {
			let mut affected_storage: Vec<(H160,H256)> = vec![];
		}

		for apply in values {
			match apply {
				Apply::Modify {
					address, basic, code, storage, reset_storage,
				} => {
					Accounts::mutate(&address, |account| {
						account.balance = basic.balance;
						account.nonce = basic.nonce;
					});

					if let Some(code) = code {
						AccountCodes::insert(address, code);
					}

					if reset_storage {
						AccountStorages::remove_prefix(address);
						#[cfg(feature = "storage_tracing")] {
							Module::<T>::deposit_event(Event::StorageReset(StorageReset(address)))
						}
					}

					for (index, value) in storage {
						if value == H256::default() {
							AccountStorages::remove(address, index);
						} else {
							AccountStorages::insert(address, index, value);
						}

						#[cfg(feature = "storage_tracing")] {
							affected_storage.push((address, index));
						}
					}

					if delete_empty {
						Module::<T>::remove_account_if_empty(&address);
					}
				},
				Apply::Delete { address } => {
					Module::<T>::remove_account(&address)
				},
			}
		}

		#[cfg(feature = "storage_tracing")] {
			if affected_storage.len() > 0 {
				affected_storage.sort();

				let mut curr_addr = None;
				let mut curr_batch: Vec<H256> = vec![];
				let mut batches: Vec<(H160, Vec<H256>)> = vec![];

				for (addr, idx) in affected_storage.into_iter() {
					if curr_addr == Some(addr) {
						curr_batch.push(idx);
					} else {
						if let Some(curr_addr) = curr_addr {
							batches.push((curr_addr, curr_batch));
						}
						curr_addr = Some(addr);
						curr_batch = vec![idx];
					}
				}

				if curr_batch.len() > 0 {
					batches.push((curr_addr.unwrap(), curr_batch));
				}

				for (address, indices) in batches.into_iter() {
					Module::<T>::deposit_event(Event::StorageWritten(StorageWritten {
						address,
						indices,
					}));
				}
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

#[derive(Clone, Eq, PartialEq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct StorageWritten {
	/// Source address of the contract affected.
	pub address: H160,
	/// Indices affected.
	pub indices: Vec<H256>,
}

#[derive(Clone, Eq, PartialEq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct StorageReset {
	/// Source address of the contract affected.
	pub address: H160,
}
