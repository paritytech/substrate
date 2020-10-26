// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Native EVM runner.

use sp_std::{
	convert::Infallible, marker::PhantomData, rc::Rc,
	collections::btree_set::BTreeSet, vec::Vec, mem, cmp::min,
};
use sp_core::{H160, U256, H256};
use sp_runtime::{TransactionOutcome, traits::UniqueSaturatedInto};
use frame_support::{
	ensure, traits::{Get, Currency, ExistenceRequirement},
	storage::{StorageMap, StorageDoubleMap},
};
use sha3::{Keccak256, Digest};
use evm::{
	ExternalOpcode, Opcode, ExitError, ExitReason, Capture, Context, CreateScheme, Stack,
	Transfer, ExitSucceed, Runtime,
};
use evm_runtime::{Config, Handler as HandlerT};
use evm_gasometer::{self as gasometer, Gasometer};
use crate::{
	Trait, Vicinity, Module, Event, Log, AccountCodes, AccountStorages, AddressMapping,
	Runner as RunnerT, Error, CallInfo, CreateInfo, FeeCalculator, precompiles::Precompiles,
};

#[derive(Default)]
pub struct Runner<T: Trait> {
	_marker: PhantomData<T>,
}

impl<T: Trait> RunnerT<T> for Runner<T> {
	type Error = Error<T>;

	fn call(
		source: H160,
		target: H160,
		input: Vec<u8>,
		value: U256,
		gas_limit: u32,
		gas_price: Option<U256>,
		nonce: Option<U256>,
	) -> Result<CallInfo, Self::Error> {
		let gas_price = match gas_price {
			Some(gas_price) => {
				ensure!(gas_price >= T::FeeCalculator::min_gas_price(), Error::<T>::GasPriceTooLow);
				gas_price
			},
			None => Default::default(),
		};

		if let Some(nonce) = nonce {
			ensure!(Module::<T>::account_basic(&source).nonce == nonce, Error::<T>::InvalidNonce);
		}

		let account_id = T::AddressMapping::into_account_id(source);
		frame_system::Module::<T>::inc_account_nonce(&account_id);

		frame_support::storage::with_transaction(|| {
			let vicinity = Vicinity {
				gas_price,
				origin: source,
			};

			let config = T::config();

			let mut substate = Handler::<T>::new_with_precompile(
				&vicinity,
				gas_limit as usize,
				false,
				config,
				T::Precompiles::execute,
			);

			let code = substate.code(target);

			let (reason, out) = substate.execute(
				source,
				target,
				value,
				code,
				input,
			);

			let used_gas = U256::from(substate.used_gas());
			let logs = substate.logs.clone();

			let call_info = CallInfo {
				exit_reason: reason.clone().into(),
				value: out,
				used_gas,
				logs,
			};

			match reason {
				ExitReason::Succeed(_) => TransactionOutcome::Commit(Ok(call_info)),
				ExitReason::Revert(_) => TransactionOutcome::Rollback(Ok(call_info)),
				ExitReason::Error(_) => TransactionOutcome::Rollback(Ok(call_info)),
				ExitReason::Fatal(_) => TransactionOutcome::Rollback(Ok(call_info)),
			}
		})
	}

	fn create(
		source: H160,
		init: Vec<u8>,
		value: U256,
		gas_limit: u32,
		gas_price: Option<U256>,
		nonce: Option<U256>,
	) -> Result<CreateInfo, Self::Error> {
		let gas_price = match gas_price {
			Some(gas_price) => {
				ensure!(gas_price >= T::FeeCalculator::min_gas_price(), Error::<T>::GasPriceTooLow);
				gas_price
			},
			None => Default::default(),
		};

		if let Some(nonce) = nonce {
			ensure!(Module::<T>::account_basic(&source).nonce == nonce, Error::<T>::InvalidNonce);
		}

		let account_id = T::AddressMapping::into_account_id(source);
		frame_system::Module::<T>::inc_account_nonce(&account_id);

		frame_support::storage::with_transaction(|| {
			let vicinity = Vicinity {
				gas_price,
				origin: source,
			};

			let config = T::config();

			let mut substate = Handler::<T>::new_with_precompile(
				&vicinity,
				gas_limit as usize,
				false,
				config,
				T::Precompiles::execute,
			);

			let address = substate.create_address(CreateScheme::Legacy { caller: source });

			let (reason, out) = substate.execute(
				source,
				address,
				value,
				init,
				Vec::new()
			);

			let used_gas = U256::from(substate.used_gas());
			let logs = substate.logs.clone();

			let mut create_info = CreateInfo {
				exit_reason: reason.clone().into(),
				value: address,
				used_gas,
				logs,
			};

			match reason {
				ExitReason::Succeed(_) => {
					match substate.gasometer.record_deposit(out.len()) {
						Ok(()) => {
							AccountCodes::insert(address, out);
							TransactionOutcome::Commit(Ok(create_info))
						},
						Err(e) => {
							create_info.exit_reason = e.into();
							TransactionOutcome::Rollback(Ok(create_info))
						},
					}
				},
				ExitReason::Revert(_) => TransactionOutcome::Rollback(Ok(create_info)),
				ExitReason::Error(_) => TransactionOutcome::Rollback(Ok(create_info)),
				ExitReason::Fatal(_) => TransactionOutcome::Rollback(Ok(create_info)),
			}
		})
	}

	fn create2(
		source: H160,
		init: Vec<u8>,
		salt: H256,
		value: U256,
		gas_limit: u32,
		gas_price: Option<U256>,
		nonce: Option<U256>,
	) -> Result<CreateInfo, Self::Error> {
		let gas_price = match gas_price {
			Some(gas_price) => {
				ensure!(gas_price >= T::FeeCalculator::min_gas_price(), Error::<T>::GasPriceTooLow);
				gas_price
			},
			None => Default::default(),
		};

		if let Some(nonce) = nonce {
			ensure!(Module::<T>::account_basic(&source).nonce == nonce, Error::<T>::InvalidNonce);
		}

		let account_id = T::AddressMapping::into_account_id(source);
		frame_system::Module::<T>::inc_account_nonce(&account_id);

		frame_support::storage::with_transaction(|| {
			let vicinity = Vicinity {
				gas_price,
				origin: source,
			};

			let config = T::config();

			let mut substate = Handler::<T>::new_with_precompile(
				&vicinity,
				gas_limit as usize,
				false,
				config,
				T::Precompiles::execute,
			);

			let code_hash = H256::from_slice(Keccak256::digest(&init).as_slice());
			let address = substate.create_address(
				CreateScheme::Create2 { caller: source, code_hash, salt }
			);

			let (reason, out) = substate.execute(
				source,
				address,
				value,
				init,
				Vec::new()
			);

			let used_gas = U256::from(substate.used_gas());
			let logs = substate.logs.clone();

			let mut create_info = CreateInfo {
				exit_reason: reason.clone().into(),
				value: address,
				used_gas,
				logs,
			};

			match reason {
				ExitReason::Succeed(_) => {
					match substate.gasometer.record_deposit(out.len()) {
						Ok(()) => {
							AccountCodes::insert(address, out);
							TransactionOutcome::Commit(Ok(create_info))
						},
						Err(e) => {
							create_info.exit_reason = e.into();
							TransactionOutcome::Rollback(Ok(create_info))
						},
					}
				},
				ExitReason::Revert(_) => TransactionOutcome::Rollback(Ok(create_info)),
				ExitReason::Error(_) => TransactionOutcome::Rollback(Ok(create_info)),
				ExitReason::Fatal(_) => TransactionOutcome::Rollback(Ok(create_info)),
			}
		})
	}
}

fn l64(gas: usize) -> usize {
	gas - gas / 64
}

pub struct Handler<'vicinity, 'config, T: Trait> {
	vicinity: &'vicinity Vicinity,
	config: &'config Config,
	gasometer: Gasometer<'config>,
	deleted: BTreeSet<H160>,
	logs: Vec<Log>,
	precompile: fn(H160, &[u8], Option<usize>) ->
		Option<Result<(ExitSucceed, Vec<u8>, usize), ExitError>>,
	is_static: bool,
	_marker: PhantomData<T>,
}

impl<'vicinity, 'config, T: Trait> Handler<'vicinity, 'config, T> {
	/// Create a new handler with given vicinity.
	pub fn new_with_precompile(
		vicinity: &'vicinity Vicinity,
		gas_limit: usize,
		is_static: bool,
		config: &'config Config,
		precompile: fn(H160, &[u8], Option<usize>) ->
			Option<Result<(ExitSucceed, Vec<u8>, usize), ExitError>>,
	) -> Self {
		Self {
			vicinity,
			config,
			is_static,
			gasometer: Gasometer::new(gas_limit, config),
			precompile,
			logs: Vec::new(),
			deleted: BTreeSet::default(),
			_marker: PhantomData,
		}
	}

	/// Get used gas for the current executor, given the price.
	pub fn used_gas(
		&self,
	) -> usize {
		self.gasometer.total_used_gas() -
			min(self.gasometer.total_used_gas() / 2, self.gasometer.refunded_gas() as usize)
	}

	pub fn execute(
		&mut self,
		caller: H160,
		address: H160,
		value: U256,
		code: Vec<u8>,
		input: Vec<u8>,
	) -> (ExitReason, Vec<u8>) {
		let context = Context {
			caller,
			address,
			apparent_value: value,
		};

		let mut runtime = Runtime::new(
			Rc::new(code),
			Rc::new(input),
			context,
			self.config,
		);

		let reason = match runtime.run(self) {
			Capture::Exit(s) => s,
			Capture::Trap(_) => unreachable!("Trap is Infallible"),
		};

		match reason {
			ExitReason::Succeed(s) => {
				(s.into(), runtime.machine().return_value())
			},
			ExitReason::Error(e) => {
				(e.into(), Vec::new())
			},
			ExitReason::Revert(e) => {
				(e.into(), runtime.machine().return_value())
			},
			ExitReason::Fatal(e) => {
				self.gasometer.fail();
				(e.into(), Vec::new())
			},
		}
	}

	fn transfer(&self, transfer: Transfer) -> Result<(), ExitError> {
		let source = T::AddressMapping::into_account_id(transfer.source);
		let target = T::AddressMapping::into_account_id(transfer.target);

		T::Currency::transfer(
			&source,
			&target,
			transfer.value.low_u128().unique_saturated_into(),
			ExistenceRequirement::AllowDeath,
		).map_err(|_| ExitError::OutOfGas)
	}

	fn nonce(&self, address: H160) -> U256 {
		let account = Module::<T>::account_basic(&address);
		account.nonce
	}

	fn inc_nonce(&self, address: H160) {
		let account_id = T::AddressMapping::into_account_id(address);
		frame_system::Module::<T>::inc_account_nonce(&account_id);
	}

	fn create_address(&self, scheme: CreateScheme) -> H160 {
		match scheme {
			CreateScheme::Create2 { caller, code_hash, salt } => {
				let mut hasher = Keccak256::new();
				hasher.input(&[0xff]);
				hasher.input(&caller[..]);
				hasher.input(&salt[..]);
				hasher.input(&code_hash[..]);
				H256::from_slice(hasher.result().as_slice()).into()
			},
			CreateScheme::Legacy { caller } => {
				let nonce = self.nonce(caller);
				let mut stream = rlp::RlpStream::new_list(2);
				stream.append(&caller);
				stream.append(&nonce);
				H256::from_slice(Keccak256::digest(&stream.out()).as_slice()).into()
			},
			CreateScheme::Fixed(naddress) => {
				naddress
			},
		}
	}
}

impl<'vicinity, 'config, T: Trait> HandlerT for Handler<'vicinity, 'config, T> {
	type CreateInterrupt = Infallible;
	type CreateFeedback = Infallible;
	type CallInterrupt = Infallible;
	type CallFeedback = Infallible;

	fn balance(&self, address: H160) -> U256 {
		let account = Module::<T>::account_basic(&address);
		account.balance
	}

	fn code_size(&self, address: H160) -> U256 {
		U256::from(AccountCodes::decode_len(&address).unwrap_or(0))
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

	fn original_storage(&self, _address: H160, _index: H256) -> H256 {
		// We do not have the concept of original storage in the native runner, so we always return
		// empty value. This only affects gas calculation in the current EVM specification.
		H256::default()
	}

	fn gas_left(&self) -> U256 {
		U256::from(self.gasometer.gas())
	}

	fn gas_price(&self) -> U256 {
		self.vicinity.gas_price
	}

	fn origin(&self) -> H160 {
		self.vicinity.origin
	}

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
		U256::from(now / 1000)
	}

	fn block_difficulty(&self) -> U256 {
		U256::zero()
	}

	fn block_gas_limit(&self) -> U256 {
		U256::zero()
	}

	fn chain_id(&self) -> U256 {
		U256::from(T::ChainId::get())
	}

	fn exists(&self, _address: H160) -> bool {
		true
	}

	fn deleted(&self, address: H160) -> bool {
		self.deleted.contains(&address)
	}

	fn set_storage(&mut self, address: H160, index: H256, value: H256) -> Result<(), ExitError> {
		if self.is_static {
			return Err(ExitError::OutOfGas)
		}

		if value == H256::default() {
			AccountStorages::remove(address, index);
		} else {
			AccountStorages::insert(address, index, value);
		}

		Ok(())
	}

	fn log(&mut self, address: H160, topics: Vec<H256>, data: Vec<u8>) -> Result<(), ExitError> {
		Module::<T>::deposit_event(Event::<T>::Log(Log {
			address,
			topics: topics.clone(),
			data: data.clone(),
		}));

		self.logs.push(Log {
			address, topics, data
		});

		Ok(())
	}

	fn mark_delete(&mut self, address: H160, target: H160) -> Result<(), ExitError> {
		if self.is_static {
			return Err(ExitError::OutOfGas)
		}

		let balance = self.balance(address);

		self.transfer(Transfer {
			source: address,
			target: target,
			value: balance
		})?;

		self.deleted.insert(address);

		Ok(())
	}

	fn create(
		&mut self,
		caller: H160,
		scheme: CreateScheme,
		value: U256,
		init_code: Vec<u8>,
		target_gas: Option<usize>,
	) -> Capture<(ExitReason, Option<H160>, Vec<u8>), Self::CreateInterrupt> {
		macro_rules! try_or_fail {
			( $e:expr ) => {
				match $e {
					Ok(v) => v,
					Err(e) => return Capture::Exit((e.into(), None, Vec::new())),
				}
			}
		}

		if self.is_static {
			return Capture::Exit((ExitError::OutOfGas.into(), None, Vec::new()))
		}

		let mut after_gas = self.gasometer.gas();
		if self.config.call_l64_after_gas {
			after_gas = l64(after_gas);
		}
		let target_gas = target_gas.unwrap_or(after_gas);
		try_or_fail!(self.gasometer.record_cost(target_gas));

		let address = self.create_address(scheme);

		frame_support::storage::with_transaction(|| {
			macro_rules! try_or_fail {
				( $e:expr ) => {
					match $e {
						Ok(v) => v,
						Err(e) => return TransactionOutcome::Rollback(
							Capture::Exit((e.into(), None, Vec::new()))
						),
					}
				}
			}

			let mut substate = Self::new_with_precompile(
				self.vicinity,
				target_gas,
				self.is_static,
				self.config,
				self.precompile,
			);

			match substate.transfer(Transfer {
				source: caller,
				target: address,
				value,
			}) {
				Ok(()) => (),
				Err(e) => return TransactionOutcome::Rollback(
					Capture::Exit((e.into(), None, Vec::new()))
				),
			}

			substate.inc_nonce(caller);

			let (reason, out) = substate.execute(
				caller,
				address,
				value,
				init_code,
				Vec::new(),
			);

			match reason {
				ExitReason::Succeed(s) => {
					match self.gasometer.record_deposit(out.len()) {
						Ok(()) => {
							try_or_fail!(
								self.gasometer.record_stipend(substate.gasometer.gas())
							);
							try_or_fail!(
								self.gasometer.record_refund(substate.gasometer.refunded_gas())
							);
							AccountCodes::insert(address, out);

							self.deleted.append(&mut substate.deleted);
							self.logs.append(&mut substate.logs);

							TransactionOutcome::Commit(
								Capture::Exit((s.into(), Some(address), Vec::new()))
							)
						},
						Err(e) => {
							TransactionOutcome::Rollback(
								Capture::Exit((e.into(), None, Vec::new()))
							)
						},
					}
				},
				ExitReason::Revert(r) => {
					TransactionOutcome::Rollback(
						Capture::Exit((r.into(), None, out))
					)
				},
				ExitReason::Error(e) => {
					TransactionOutcome::Rollback(
						Capture::Exit((e.into(), None, Vec::new()))
					)
				},
				ExitReason::Fatal(e) => {
					self.gasometer.fail();
					TransactionOutcome::Rollback(
						Capture::Exit((e.into(), None, Vec::new()))
					)
				},
			}
		})
	}

	fn call(
		&mut self,
		code_address: H160,
		transfer: Option<Transfer>,
		input: Vec<u8>,
		target_gas: Option<usize>,
		is_static: bool,
		context: Context,
	) -> Capture<(ExitReason, Vec<u8>), Self::CallInterrupt> {
		macro_rules! try_or_fail {
			( $e:expr ) => {
				match $e {
					Ok(v) => v,
					Err(e) => return Capture::Exit((e.into(), Vec::new())),
				}
			}
		}

		if self.is_static && transfer.is_some() {
			return Capture::Exit((ExitError::OutOfGas.into(), Vec::new()))
		}

		let mut after_gas = self.gasometer.gas();
		if self.config.call_l64_after_gas {
			after_gas = l64(after_gas);
		}
		let target_gas = target_gas.unwrap_or(after_gas);
		try_or_fail!(self.gasometer.record_cost(target_gas));

		let code = self.code(code_address);

		frame_support::storage::with_transaction(|| {
			macro_rules! try_or_fail {
				( $e:expr ) => {
					match $e {
						Ok(v) => v,
						Err(e) => return TransactionOutcome::Rollback(
							Capture::Exit((e.into(), Vec::new()))
						),
					}
				}
			}

			let mut substate = Self::new_with_precompile(
				self.vicinity,
				target_gas,
				self.is_static || is_static,
				self.config,
				self.precompile,
			);

			if let Some(transfer) = transfer {
				match substate.transfer(transfer) {
					Ok(()) => (),
					Err(e) => return TransactionOutcome::Rollback(
						Capture::Exit((e.into(), Vec::new()))
					),
				}
			}

			let (reason, out) = substate.execute(
				context.caller,
				context.address,
				context.apparent_value,
				code,
				input,
			);

			match reason {
				ExitReason::Succeed(s) => {
					try_or_fail!(
						self.gasometer.record_stipend(substate.gasometer.gas())
					);
					try_or_fail!(
						self.gasometer.record_refund(substate.gasometer.refunded_gas())
					);

					self.deleted.append(&mut substate.deleted);
					self.logs.append(&mut substate.logs);

					TransactionOutcome::Commit(
						Capture::Exit((s.into(), out))
					)
				},
				ExitReason::Revert(r) => {
					TransactionOutcome::Rollback(
						Capture::Exit((r.into(), out))
					)
				},
				ExitReason::Error(e) => {
					TransactionOutcome::Rollback(
						Capture::Exit((e.into(), Vec::new()))
					)
				},
				ExitReason::Fatal(e) => {
					self.gasometer.fail();
					TransactionOutcome::Rollback(
						Capture::Exit((e.into(), Vec::new()))
					)
				},
			}
		})
	}

	fn pre_validate(
		&mut self,
		context: &Context,
		opcode: Result<Opcode, ExternalOpcode>,
		stack: &Stack
	) -> Result<(), ExitError> {
		let (gas_cost, memory_cost) = gasometer::opcode_cost(
			context.address, opcode, stack, self.is_static, &self.config, self
		)?;

		self.gasometer.record_opcode(gas_cost, memory_cost)?;

		Ok(())
	}
}

impl<'vicinity, 'config, T: Trait> Drop for Handler<'vicinity, 'config, T> {
	fn drop(&mut self) {
		let mut deleted = BTreeSet::new();
		mem::swap(&mut deleted, &mut self.deleted);

		for address in deleted {
			Module::<T>::remove_account(&address);
		}
	}
}
