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

use sp_std::{convert::Infallible, marker::PhantomData, collections::btree_set::BTreeSet};
use sp_core::{H160, U256, H256};
use sp_runtime::traits::UniqueSaturatedInto;
use frame_support::{ensure, traits::{Get, Currency, ExistenceRequirement}, storage::{StorageMap, StorageDoubleMap}};
use sha3::{Keccak256, Digest};
use evm::{
	ExternalOpcode, Opcode, ExitError, ExitReason, Capture, Context, CreateScheme, Stack,
	Transfer, ExitSucceed,
};
use evm_runtime::{Config, Handler as HandlerT};
use evm_gasometer::Gasometer;
use crate::{
	Trait, Vicinity, Module, Event, Runner, Log, AccountCodes, AccountStorages, AddressMapping,
	CreateInfo,
};

fn l64(gas: usize) -> usize {
	gas - gas / 64
}

pub struct Handler<'vicinity, 'config, T> {
	vicinity: &'vicinity Vicinity,
	config: &'config Config,
	gasometer: Gasometer<'config>,
	deleted: BTreeSet<H160>,
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
		config: &'config Config,
		precompile: fn(H160, &[u8], Option<usize>) ->
			Option<Result<(ExitSucceed, Vec<u8>, usize), ExitError>>,
	) -> Self {
		Self {
			vicinity,
			config,
			gasometer: Gasometer::new(gas_limit, config),
			precompile,
			deleted: BTreeSet::default(),
			_marker: PhantomData,
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

	fn original_storage(&self, address: H160, index: H256) -> H256 {
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

	fn exists(&self, address: H160) -> bool {
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
			topics,
			data,
		}));

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
		if self.is_static {
			return Err(ExitError::OutOfGas)
		}

		let mut after_gas = self.gasometer.gas();
		if self.config.call_l64_after_gas {
			after_gas = l64(after_gas);
		}
		let target_gas = target_gas.unwrap_or(after_gas);

		let called = match scheme {
			CreateScheme::Legacy { caller } =>
				T::Runner::create(
					caller,
					init_code,
					value,
					target_gas as u32,
					self.vicinity.gas_price,
					None,
				),
			CreateScheme::Create2 { caller, salt, code_hash: _ } => {
				T::Runner::create2(
					caller,
					init_code,
					salt,
					value,
					target_gas as u32,
					self.vicinity.gas_price,
					None
				)
			},
			CreateScheme::Fixed(_) => return Capture::Exit(
				(ExitError::OutOfGas.into(), None, Vec::new())
			),
		};

		match called {
			Ok(CreateInfo {
				exit_reason,
				value: address,
				used_gas,
				logs: _,
			}) => {
				match self.gasometer.record_cost(used_gas.low_u128().unique_saturated_into()) {
					Ok(()) => (),
					Err(e) => return Capture::Exit((e.into(), None, Vec::new())),
				}

				match exit_reason {
					ExitReason::Succeed(e) => Capture::Exit((e.into(), Some(address), Vec::new())),
					ExitReason::Revert(e) => Capture::Exit((e.into(), None, Vec::new())),
					ExitReason::Error(e) => Capture::Exit((e.into(), None, Vec::new())),
					ExitReason::Fatal(e) => Capture::Exit((e.into(), None, Vec::new())),
				}
			},
			Err(e) => {
				self.gasometer.fail();
				Capture::Exit((ExitError::OutOfGas.into(), None, Vec::new()))
			},
		}
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
		unimplemented!()
	}

	fn pre_validate(
		&mut self,
		context: &Context,
		opcode: Result<Opcode, ExternalOpcode>,
		stack: &Stack
	) -> Result<(), ExitError> {
		unimplemented!()
	}
}
