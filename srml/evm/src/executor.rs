use rstd::vec::Vec;
#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use codec::{Encode, Decode};
use primitives::{U256, H256, H160};
use rstd::collections::{
	btree_map::BTreeMap as Map, btree_set::BTreeSet as Set
};
use support::storage::StorageMap;
use sha3::{Keccak256, Digest};
use core::convert::Infallible;
use core::cmp::min;
use alloc::rc::Rc;
use evm::{CreateScheme, Handler, ExitError, ExternalOpcode, Opcode, Stack,
		  Memory, Context, Capture, Runtime, ExitReason};
use evm::gasometer::{self, Gasometer};
use crate::{Trait, Accounts, Module, Event};

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct Account {
	pub nonce: U256,
	pub balance: U256,
	pub code: Vec<u8>,
	pub storage: Map<H256, H256>,
}

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default)]
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

pub static GASOMETER_CONFIG: gasometer::Config = gasometer::Config::frontier();
pub const STACK_LIMIT: usize = 1024;
pub const MEMORY_LIMIT: usize = 1000000;

pub struct Executor<'vicinity> {
	gasometer: Gasometer<'static>,
	state: Map<H160, Account>,
	deleted: Set<H160>,
	logs: Vec<Log>,
	vicinity: &'vicinity Vicinity,
}

impl<'vicinity> Executor<'vicinity> {
	pub fn new(
		vicinity: &'vicinity Vicinity,
		gas_limit: usize
	) -> Self {
		Self {
			state: Map::new(),
			vicinity,
			deleted: Set::new(),
			logs: Vec::new(),
			gasometer: Gasometer::new(gas_limit, &GASOMETER_CONFIG),
		}
	}

	pub fn execute(&mut self, runtime: &mut Runtime) -> ExitReason {
		match runtime.run(self) {
			Capture::Exit(reason) => reason,
			Capture::Trap(_) => unreachable!("Trap is Infallible"),
		}
	}

	pub fn gas(&self) -> usize {
		self.gasometer.gas()
	}

	pub fn apply<T: Trait>(self) {
		for (address, account) in self.state {
			Accounts::insert(address, account);
		}

		for address in self.deleted {
			Accounts::remove(address);
		}

		for log in self.logs {
			Module::<T>::deposit_event(Event::Log(log));
		}
	}

	fn account(&self, address: H160) -> Account {
		self.state.get(&address).map(|a| a.clone()) // TODO: remove this clone
			.unwrap_or(Accounts::get(address))
	}

	fn account_mut(&mut self, address: H160) -> &mut Account {
		self.state.entry(address).or_insert(Accounts::get(address))
	}
}

impl<'vicinity> Handler for Executor<'vicinity> {
	type CreateInterrupt = Infallible;
	type CreateFeedback = Infallible;
	type CallInterrupt = Infallible;
	type CallFeedback = Infallible;

	fn balance(&self, address: H160) -> U256 {
		self.account(address).balance
	}

	fn code_size(&self, address: H160) -> U256 {
		U256::from(self.account(address).code.len())
	}

	fn code_hash(&self, address: H160) -> H256 {
		H256::from_slice(Keccak256::digest(&self.account(address).code).as_slice())
	}

	fn code(&self, address: H160) -> Vec<u8> {
		self.account(address).code.clone()
	}

	fn storage(&self, address: H160, index: H256) -> H256 {
		self.account(address).storage.get(&index).cloned().unwrap_or_default()
	}

	fn original_storage(&self, address: H160, index: H256) -> H256 {
		Accounts::get(address).storage.get(&index).cloned().unwrap_or_default()
	}

	fn gas_left(&self) -> U256 { U256::from(self.gasometer.gas()) }
	fn gas_price(&self) -> U256 { self.vicinity.gas_price }
	fn origin(&self) -> H160 { self.vicinity.origin }

	fn block_hash(&self, number: U256) -> H256 {
		H256::default() // TODO: use system::BlockHash
	}

	fn block_number(&self) -> U256 {
		U256::zero() // TODO: use system::Number
	}

	fn block_coinbase(&self) -> H160 {
		H160::default() // TODO: allow customization of this value
	}

	fn block_timestamp(&self) -> U256 {
		U256::zero() // TODO: use timestamp
	}

	fn block_difficulty(&self) -> U256 {
		U256::zero() // TODO: allow customization of this value
	}

	fn block_gas_limit(&self) -> U256 {
		U256::zero() // TODO: allow customization of this value
	}

	fn create_address(&mut self, address: H160, scheme: CreateScheme) -> Result<H160, ExitError> {
		match scheme {
			CreateScheme::Fixed(address) => Ok(address),
			CreateScheme::Dynamic => {
				let nonce = self.account(address).nonce;
				self.account_mut(address).nonce += U256::one();
				let mut stream = rlp::RlpStream::new_list(2);
				stream.append(&address);
				stream.append(&nonce);
				Ok(H256::from_slice(Keccak256::digest(&stream.out()).as_slice()).into())
			},
		}
	}

	fn exists(&self, address: H160) -> bool {
		let account = self.account(address);

		account.nonce != U256::zero() ||
			account.balance != U256::zero() ||
			account.code.len() != 0
	}

	fn deleted(&self, address: H160) -> bool { self.deleted.contains(&address) }

	fn is_recoverable(&self) -> bool { true }

	fn set_storage(&mut self, address: H160, index: H256, value: H256) -> Result<(), ExitError> {
		let account = self.account_mut(address);
		if value == H256::zero() {
			account.storage.remove(&index);
		} else {
			account.storage.insert(index, value);
		}
		Ok(())
	}

	fn log(&mut self, address: H160, topics: Vec<H256>, data: Vec<u8>) -> Result<(), ExitError> {
		self.logs.push(Log {
			address, topics, data
		});

		Ok(())
	}

	fn transfer(&mut self, source: H160, target: H160, value: U256) -> Result<(), ExitError> {
		if value == U256::zero() {
			return Ok(())
		}

		{
			let source = self.account_mut(source);

			if source.balance < value {
				return Err(ExitError::Other("not enough fund"))
			}

			source.balance -= value;
		}

		{
			let target = self.account_mut(target);

			target.balance += value;
		}

		Ok(())
	}

	fn mark_delete(&mut self, address: H160) -> Result<(), ExitError> {
		self.deleted.insert(address);

		Ok(())
	}

	fn create(
		&mut self,
		address: H160,
		init_code: Vec<u8>,
		target_gas: Option<usize>,
		context: Context,
	) -> Result<Capture<(), Self::CreateInterrupt>, ExitError> {
		let after_gas = self.gasometer.gas(); // TODO: support l64(after_gas)
		let target_gas = target_gas.unwrap_or(after_gas);

		let gas_limit = min(after_gas, target_gas);

		let mut substate = Self::new(
			self.vicinity,
			gas_limit,
		);
		substate.state.insert(address, Default::default());

		let mut runtime = Runtime::new(
			Rc::new(init_code),
			Rc::new(Vec::new()),
			STACK_LIMIT,
			MEMORY_LIMIT,
			context,
		);

		let reason = substate.execute(&mut runtime);

		self.gasometer.merge(substate.gasometer)?;
		self.logs.append(&mut substate.logs);

		match reason {
			ExitReason::Succeed(_) => {
				self.deleted.intersection(&substate.deleted);
				self.state = substate.state;
				self.account(address).code = runtime.machine().return_value();

				Ok(Capture::Exit(()))
			},
			ExitReason::Error(e) => {
				Err(e)
			},
		}
	}

	fn call(
		&mut self,
		code_address: H160,
		input: Vec<u8>,
		target_gas: Option<usize>,
		_is_static: bool, // TODO: support this
		context: Context,
	) -> Result<Capture<Vec<u8>, Self::CallInterrupt>, ExitError> {
		let after_gas = self.gasometer.gas(); // TODO: support l64(after_gas)
		let target_gas = target_gas.unwrap_or(after_gas);
		let code = self.code(code_address);

		let gas_limit = min(after_gas, target_gas);
		let mut substate = Self::new(
			self.vicinity,
			gas_limit,
		);
		let mut runtime = Runtime::new(
			Rc::new(code),
			Rc::new(input),
			STACK_LIMIT,
			MEMORY_LIMIT,
			context,
		);

		let reason = substate.execute(&mut runtime);

		self.gasometer.merge(substate.gasometer)?;
		self.logs.append(&mut substate.logs);

		match reason {
			ExitReason::Succeed(_) => {
				self.deleted.intersection(&substate.deleted);
				self.state = substate.state;

				Ok(Capture::Exit(runtime.machine().return_value()))
			},
			ExitReason::Error(e) => {
				Err(e)
			},
		}
	}

	fn pre_validate(
		&mut self,
		context: &Context,
		opcode: Result<Opcode, ExternalOpcode>,
		stack: &Stack
	) -> Result<(), ExitError> {
		// TODO: Add opcode check.
		let (gas_cost, memory_cost) = gasometer::cost(context.address, opcode, stack, self)?;
		self.gasometer.record(gas_cost, memory_cost)?;

		Ok(())
	}
}
