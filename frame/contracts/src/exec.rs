// Copyright 2018-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

use crate::{
	CodeHash, Config, ContractAddressFor, Event, RawEvent, Trait,
	TrieId, BalanceOf, ContractInfo, TrieIdGenerator,
	gas::GasMeter, rent, storage, Error, ContractInfoOf
};
use sp_std::prelude::*;
use sp_runtime::traits::{Bounded, Zero, Convert, Saturating};
use frame_support::{
	dispatch::DispatchError,
	traits::{ExistenceRequirement, Currency, Time, Randomness},
	weights::Weight,
	ensure, StorageMap,
};
use pallet_contracts_primitives::{ErrorOrigin, ExecError, ExecReturnValue, ExecResult, ReturnFlags};

pub type AccountIdOf<T> = <T as frame_system::Trait>::AccountId;
pub type MomentOf<T> = <<T as Trait>::Time as Time>::Moment;
pub type SeedOf<T> = <T as frame_system::Trait>::Hash;
pub type BlockNumberOf<T> = <T as frame_system::Trait>::BlockNumber;
pub type StorageKey = [u8; 32];

/// A type that represents a topic of an event. At the moment a hash is used.
pub type TopicOf<T> = <T as frame_system::Trait>::Hash;

/// Describes whether we deal with a contract or a plain account.
pub enum TransactorKind {
	/// Transaction was initiated from a plain account. That can be either be through a
	/// signed transaction or through RPC.
	PlainAccount,
	/// The call was initiated by a contract account.
	Contract,
}

/// An interface that provides access to the external environment in which the
/// smart-contract is executed.
///
/// This interface is specialized to an account of the executing code, so all
/// operations are implicitly performed on that account.
pub trait Ext {
	type T: Trait;

	/// Returns the storage entry of the executing account by the given `key`.
	///
	/// Returns `None` if the `key` wasn't previously set by `set_storage` or
	/// was deleted.
	fn get_storage(&self, key: &StorageKey) -> Option<Vec<u8>>;

	/// Sets the storage entry by the given key to the specified value. If `value` is `None` then
	/// the storage entry is deleted.
	fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>);

	/// Instantiate a contract from the given code.
	///
	/// The newly created account will be associated with `code`. `value` specifies the amount of value
	/// transferred from this to the newly created account (also known as endowment).
	fn instantiate(
		&mut self,
		code: &CodeHash<Self::T>,
		value: BalanceOf<Self::T>,
		gas_meter: &mut GasMeter<Self::T>,
		input_data: Vec<u8>,
	) -> Result<(AccountIdOf<Self::T>, ExecReturnValue), ExecError>;

	/// Transfer some amount of funds into the specified account.
	fn transfer(
		&mut self,
		to: &AccountIdOf<Self::T>,
		value: BalanceOf<Self::T>,
	) -> Result<(), DispatchError>;

	/// Transfer all funds to `beneficiary` and delete the contract.
	///
	/// Since this function removes the self contract eagerly, if succeeded, no further actions should
	/// be performed on this `Ext` instance.
	///
	/// This function will fail if the same contract is present on the contract
	/// call stack.
	fn terminate(
		&mut self,
		beneficiary: &AccountIdOf<Self::T>,
	) -> Result<(), DispatchError>;

	/// Call (possibly transferring some amount of funds) into the specified account.
	fn call(
		&mut self,
		to: &AccountIdOf<Self::T>,
		value: BalanceOf<Self::T>,
		gas_meter: &mut GasMeter<Self::T>,
		input_data: Vec<u8>,
	) -> ExecResult;

	/// Restores the given destination contract sacrificing the current one.
	///
	/// Since this function removes the self contract eagerly, if succeeded, no further actions should
	/// be performed on this `Ext` instance.
	///
	/// This function will fail if the same contract is present
	/// on the contract call stack.
	fn restore_to(
		&mut self,
		dest: AccountIdOf<Self::T>,
		code_hash: CodeHash<Self::T>,
		rent_allowance: BalanceOf<Self::T>,
		delta: Vec<StorageKey>,
	) -> Result<(), &'static str>;

	/// Returns a reference to the account id of the caller.
	fn caller(&self) -> &AccountIdOf<Self::T>;

	/// Returns a reference to the account id of the current contract.
	fn address(&self) -> &AccountIdOf<Self::T>;

	/// Returns the balance of the current contract.
	///
	/// The `value_transferred` is already added.
	fn balance(&self) -> BalanceOf<Self::T>;

	/// Returns the value transferred along with this call or as endowment.
	fn value_transferred(&self) -> BalanceOf<Self::T>;

	/// Returns a reference to the timestamp of the current block
	fn now(&self) -> &MomentOf<Self::T>;

	/// Returns the minimum balance that is required for creating an account.
	fn minimum_balance(&self) -> BalanceOf<Self::T>;

	/// Returns the deposit required to create a tombstone upon contract eviction.
	fn tombstone_deposit(&self) -> BalanceOf<Self::T>;

	/// Returns a random number for the current block with the given subject.
	fn random(&self, subject: &[u8]) -> SeedOf<Self::T>;

	/// Deposit an event with the given topics.
	///
	/// There should not be any duplicates in `topics`.
	fn deposit_event(&mut self, topics: Vec<TopicOf<Self::T>>, data: Vec<u8>);

	/// Set rent allowance of the contract
	fn set_rent_allowance(&mut self, rent_allowance: BalanceOf<Self::T>);

	/// Rent allowance of the contract
	fn rent_allowance(&self) -> BalanceOf<Self::T>;

	/// Returns the current block number.
	fn block_number(&self) -> BlockNumberOf<Self::T>;

	/// Returns the maximum allowed size of a storage item.
	fn max_value_size(&self) -> u32;

	/// Returns the price for the specified amount of weight.
	fn get_weight_price(&self, weight: Weight) -> BalanceOf<Self::T>;
}

/// Loader is a companion of the `Vm` trait. It loads an appropriate abstract
/// executable to be executed by an accompanying `Vm` implementation.
pub trait Loader<T: Trait> {
	type Executable;

	/// Load the initializer portion of the code specified by the `code_hash`. This
	/// executable is called upon instantiation.
	fn load_init(&self, code_hash: &CodeHash<T>) -> Result<Self::Executable, &'static str>;
	/// Load the main portion of the code specified by the `code_hash`. This executable
	/// is called for each call to a contract.
	fn load_main(&self, code_hash: &CodeHash<T>) -> Result<Self::Executable, &'static str>;
}

/// A trait that represent a virtual machine.
///
/// You can view a virtual machine as something that takes code, an input data buffer,
/// queries it and/or performs actions on the given `Ext` and optionally
/// returns an output data buffer. The type of code depends on the particular virtual machine.
///
/// Execution of code can end by either implicit termination (that is, reached the end of
/// executable), explicit termination via returning a buffer or termination due to a trap.
pub trait Vm<T: Trait> {
	type Executable;

	fn execute<E: Ext<T = T>>(
		&self,
		exec: &Self::Executable,
		ext: E,
		input_data: Vec<u8>,
		gas_meter: &mut GasMeter<T>,
	) -> ExecResult;
}

pub struct ExecutionContext<'a, T: Trait + 'a, V, L> {
	pub caller: Option<&'a ExecutionContext<'a, T, V, L>>,
	pub self_account: T::AccountId,
	pub self_trie_id: Option<TrieId>,
	pub depth: usize,
	pub config: &'a Config<T>,
	pub vm: &'a V,
	pub loader: &'a L,
	pub timestamp: MomentOf<T>,
	pub block_number: T::BlockNumber,
}

impl<'a, T, E, V, L> ExecutionContext<'a, T, V, L>
where
	T: Trait,
	L: Loader<T, Executable = E>,
	V: Vm<T, Executable = E>,
{
	/// Create the top level execution context.
	///
	/// The specified `origin` address will be used as `sender` for. The `origin` must be a regular
	/// account (not a contract).
	pub fn top_level(origin: T::AccountId, cfg: &'a Config<T>, vm: &'a V, loader: &'a L) -> Self {
		ExecutionContext {
			caller: None,
			self_trie_id: None,
			self_account: origin,
			depth: 0,
			config: &cfg,
			vm: &vm,
			loader: &loader,
			timestamp: T::Time::now(),
			block_number: <frame_system::Module<T>>::block_number(),
		}
	}

	fn nested<'b, 'c: 'b>(&'c self, dest: T::AccountId, trie_id: TrieId)
		-> ExecutionContext<'b, T, V, L>
	{
		ExecutionContext {
			caller: Some(self),
			self_trie_id: Some(trie_id),
			self_account: dest,
			depth: self.depth + 1,
			config: self.config,
			vm: self.vm,
			loader: self.loader,
			timestamp: self.timestamp.clone(),
			block_number: self.block_number.clone(),
		}
	}

	/// Make a call to the specified address, optionally transferring some funds.
	pub fn call(
		&mut self,
		dest: T::AccountId,
		value: BalanceOf<T>,
		gas_meter: &mut GasMeter<T>,
		input_data: Vec<u8>,
	) -> ExecResult {
		if self.depth == self.config.max_depth as usize {
			Err(Error::<T>::MaxCallDepthReached)?
		}

		// Assumption: `collect_rent` doesn't collide with overlay because
		// `collect_rent` will be done on first call and destination contract and balance
		// cannot be changed before the first call
		// We do not allow 'calling' plain accounts. For transfering value
		// `seal_transfer` must be used.
		let contract = if let Some(ContractInfo::Alive(info)) = rent::collect_rent::<T>(&dest) {
			info
		} else {
			Err(Error::<T>::NotCallable)?
		};

		let transactor_kind = self.transactor_kind();
		let caller = self.self_account.clone();

		self.with_nested_context(dest.clone(), contract.trie_id.clone(), |nested| {
			if value > BalanceOf::<T>::zero() {
				transfer(
					TransferCause::Call,
					transactor_kind,
					&caller,
					&dest,
					value,
					nested,
				)?
			}

			let executable = nested.loader.load_main(&contract.code_hash)
				.map_err(|_| Error::<T>::CodeNotFound)?;
			let output = nested.vm.execute(
				&executable,
				nested.new_call_context(caller, value),
				input_data,
				gas_meter,
			).map_err(|e| ExecError { error: e.error, origin: ErrorOrigin::Callee })?;
			Ok(output)
		})
	}

	pub fn instantiate(
		&mut self,
		endowment: BalanceOf<T>,
		gas_meter: &mut GasMeter<T>,
		code_hash: &CodeHash<T>,
		input_data: Vec<u8>,
	) -> Result<(T::AccountId, ExecReturnValue), ExecError> {
		if self.depth == self.config.max_depth as usize {
			Err(Error::<T>::MaxCallDepthReached)?
		}

		let transactor_kind = self.transactor_kind();
		let caller = self.self_account.clone();
		let dest = T::DetermineContractAddress::contract_address_for(
			code_hash,
			&input_data,
			&caller,
		);

		// TrieId has not been generated yet and storage is empty since contract is new.
		//
		// Generate it now.
		let dest_trie_id = <T as Trait>::TrieIdGenerator::trie_id(&dest);

		let output = self.with_nested_context(dest.clone(), dest_trie_id, |nested| {
			storage::place_contract::<T>(
				&dest,
				nested
					.self_trie_id
					.clone()
					.expect("the nested context always has to have self_trie_id"),
				code_hash.clone()
			)?;

			// Send funds unconditionally here. If the `endowment` is below existential_deposit
			// then error will be returned here.
			transfer(
				TransferCause::Instantiate,
				transactor_kind,
				&caller,
				&dest,
				endowment,
				nested,
			)?;

			let executable = nested.loader.load_init(&code_hash)
				.map_err(|_| Error::<T>::CodeNotFound)?;
			let output = nested.vm
				.execute(
					&executable,
					nested.new_call_context(caller.clone(), endowment),
					input_data,
					gas_meter,
				).map_err(|e| ExecError { error: e.error, origin: ErrorOrigin::Callee })?;

			// We need each contract that exists to be above the subsistence threshold
			// in order to keep up the guarantuee that we always leave a tombstone behind
			// with the exception of a contract that called `seal_terminate`.
			if T::Currency::total_balance(&dest) < nested.config.subsistence_threshold() {
				Err(Error::<T>::NewContractNotFunded)?
			}

			// Deposit an instantiation event.
			deposit_event::<T>(vec![], RawEvent::Instantiated(caller.clone(), dest.clone()));

			Ok(output)
		})?;

		Ok((dest, output))
	}

	fn new_call_context<'b>(
		&'b mut self,
		caller: T::AccountId,
		value: BalanceOf<T>,
	) -> CallContext<'b, 'a, T, V, L> {
		let timestamp = self.timestamp.clone();
		let block_number = self.block_number.clone();
		CallContext {
			ctx: self,
			caller,
			value_transferred: value,
			timestamp,
			block_number,
		}
	}

	/// Execute the given closure within a nested execution context.
	fn with_nested_context<F>(&mut self, dest: T::AccountId, trie_id: TrieId, func: F)
		-> ExecResult
		where F: FnOnce(&mut ExecutionContext<T, V, L>) -> ExecResult
	{
		use frame_support::storage::TransactionOutcome::*;
		let mut nested = self.nested(dest, trie_id);
		frame_support::storage::with_transaction(|| {
			let output = func(&mut nested);
			match output {
				Ok(ref rv) if !rv.flags.contains(ReturnFlags::REVERT) => Commit(output),
				_ => Rollback(output),
			}
		})
	}

	/// Returns whether a contract, identified by address, is currently live in the execution
	/// stack, meaning it is in the middle of an execution.
	fn is_live(&self, account: &T::AccountId) -> bool {
		&self.self_account == account ||
			self.caller.map_or(false, |caller| caller.is_live(account))
	}

	fn transactor_kind(&self) -> TransactorKind {
		if self.depth == 0 {
			debug_assert!(self.self_trie_id.is_none());
			debug_assert!(self.caller.is_none());
			debug_assert!(ContractInfoOf::<T>::get(&self.self_account).is_none());
			TransactorKind::PlainAccount
		} else {
			TransactorKind::Contract
		}
	}
}

/// Describes possible transfer causes.
enum TransferCause {
	Call,
	Instantiate,
	Terminate,
}

/// Transfer some funds from `transactor` to `dest`.
///
/// We only allow allow for draining all funds of the sender if `cause` is
/// is specified as `Terminate`. Otherwise, any transfer that would bring the sender below the
/// subsistence threshold (for contracts) or the existential deposit (for plain accounts)
/// results in an error.
fn transfer<'a, T: Trait, V: Vm<T>, L: Loader<T>>(
	cause: TransferCause,
	origin: TransactorKind,
	transactor: &T::AccountId,
	dest: &T::AccountId,
	value: BalanceOf<T>,
	ctx: &mut ExecutionContext<'a, T, V, L>,
) -> Result<(), DispatchError> {
	use self::TransferCause::*;
	use self::TransactorKind::*;

	// Only seal_terminate is allowed to bring the sender below the subsistence
	// threshold or even existential deposit.
	let existence_requirement = match (cause, origin) {
		(Terminate, _) => ExistenceRequirement::AllowDeath,
		(_, Contract) => {
			ensure!(
				T::Currency::total_balance(transactor).saturating_sub(value) >=
					ctx.config.subsistence_threshold(),
				Error::<T>::BelowSubsistenceThreshold,
			);
			ExistenceRequirement::KeepAlive
		},
		(_, PlainAccount) => ExistenceRequirement::KeepAlive,
	};

	T::Currency::transfer(transactor, dest, value, existence_requirement)
		.map_err(|_| Error::<T>::TransferFailed)?;

	Ok(())
}

/// A context that is active within a call.
///
/// This context has some invariants that must be held at all times. Specifically:
///`ctx` always points to a context of an alive contract. That implies that it has an existent
/// `self_trie_id`.
///
/// Be advised that there are brief time spans where these invariants could be invalidated.
/// For example, when a contract requests self-termination the contract is removed eagerly. That
/// implies that the control won't be returned to the contract anymore, but there is still some code
/// on the path of the return from that call context. Therefore, care must be taken in these
/// situations.
struct CallContext<'a, 'b: 'a, T: Trait + 'b, V: Vm<T> + 'b, L: Loader<T>> {
	ctx: &'a mut ExecutionContext<'b, T, V, L>,
	caller: T::AccountId,
	value_transferred: BalanceOf<T>,
	timestamp: MomentOf<T>,
	block_number: T::BlockNumber,
}

impl<'a, 'b: 'a, T, E, V, L> Ext for CallContext<'a, 'b, T, V, L>
where
	T: Trait + 'b,
	V: Vm<T, Executable = E>,
	L: Loader<T, Executable = E>,
{
	type T = T;

	fn get_storage(&self, key: &StorageKey) -> Option<Vec<u8>> {
		let trie_id = self.ctx.self_trie_id.as_ref().expect(
			"`ctx.self_trie_id` points to an alive contract within the `CallContext`;\
				it cannot be `None`;\
				expect can't fail;\
				qed",
		);
		storage::read_contract_storage(trie_id, key)
	}

	fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>) {
		let trie_id = self.ctx.self_trie_id.as_ref().expect(
			"`ctx.self_trie_id` points to an alive contract within the `CallContext`;\
				it cannot be `None`;\
				expect can't fail;\
				qed",
		);
		if let Err(storage::ContractAbsentError) =
			storage::write_contract_storage::<T>(&self.ctx.self_account, trie_id, &key, value)
		{
			panic!(
				"the contract must be in the alive state within the `CallContext`;\
				the contract cannot be absent in storage;
				write_contract_storage cannot return `None`;
				qed"
			);
		}
	}

	fn instantiate(
		&mut self,
		code_hash: &CodeHash<T>,
		endowment: BalanceOf<T>,
		gas_meter: &mut GasMeter<T>,
		input_data: Vec<u8>,
	) -> Result<(AccountIdOf<T>, ExecReturnValue), ExecError> {
		self.ctx.instantiate(endowment, gas_meter, code_hash, input_data)
	}

	fn transfer(
		&mut self,
		to: &T::AccountId,
		value: BalanceOf<T>,
	) -> Result<(), DispatchError> {
		transfer(
			TransferCause::Call,
			TransactorKind::Contract,
			&self.ctx.self_account.clone(),
			to,
			value,
			self.ctx,
		)
	}

	fn terminate(
		&mut self,
		beneficiary: &AccountIdOf<Self::T>,
	) -> Result<(), DispatchError> {
		let self_id = self.ctx.self_account.clone();
		let value = T::Currency::free_balance(&self_id);
		if let Some(caller_ctx) = self.ctx.caller {
			if caller_ctx.is_live(&self_id) {
				return Err(DispatchError::Other(
					"Cannot terminate a contract that is present on the call stack",
				));
			}
		}
		transfer(
			TransferCause::Terminate,
			TransactorKind::Contract,
			&self_id,
			beneficiary,
			value,
			self.ctx,
		)?;
		let self_trie_id = self.ctx.self_trie_id.as_ref().expect(
			"this function is only invoked by in the context of a contract;\
				a contract has a trie id;\
				this can't be None; qed",
		);
		storage::destroy_contract::<T>(&self_id, self_trie_id);
		Ok(())
	}

	fn call(
		&mut self,
		to: &T::AccountId,
		value: BalanceOf<T>,
		gas_meter: &mut GasMeter<T>,
		input_data: Vec<u8>,
	) -> ExecResult {
		self.ctx.call(to.clone(), value, gas_meter, input_data)
	}

	fn restore_to(
		&mut self,
		dest: AccountIdOf<Self::T>,
		code_hash: CodeHash<Self::T>,
		rent_allowance: BalanceOf<Self::T>,
		delta: Vec<StorageKey>,
	) -> Result<(), &'static str> {
		if let Some(caller_ctx) = self.ctx.caller {
			if caller_ctx.is_live(&self.ctx.self_account) {
				return Err(
					"Cannot perform restoration of a contract that is present on the call stack",
				);
			}
		}

		let result = crate::rent::restore_to::<T>(
			self.ctx.self_account.clone(),
			dest.clone(),
			code_hash.clone(),
			rent_allowance,
			delta,
		);
		if let Ok(_) = result {
			deposit_event::<Self::T>(
				vec![],
				RawEvent::Restored(
					self.ctx.self_account.clone(),
					dest,
					code_hash,
					rent_allowance,
				),
			);
		}
		result
	}

	fn address(&self) -> &T::AccountId {
		&self.ctx.self_account
	}

	fn caller(&self) -> &T::AccountId {
		&self.caller
	}

	fn balance(&self) -> BalanceOf<T> {
		T::Currency::free_balance(&self.ctx.self_account)
	}

	fn value_transferred(&self) -> BalanceOf<T> {
		self.value_transferred
	}

	fn random(&self, subject: &[u8]) -> SeedOf<T> {
		T::Randomness::random(subject)
	}

	fn now(&self) -> &MomentOf<T> {
		&self.timestamp
	}

	fn minimum_balance(&self) -> BalanceOf<T> {
		self.ctx.config.existential_deposit
	}

	fn tombstone_deposit(&self) -> BalanceOf<T> {
		self.ctx.config.tombstone_deposit
	}

	fn deposit_event(&mut self, topics: Vec<T::Hash>, data: Vec<u8>) {
		deposit_event::<Self::T>(
			topics,
			RawEvent::ContractExecution(self.ctx.self_account.clone(), data)
		);
	}

	fn set_rent_allowance(&mut self, rent_allowance: BalanceOf<T>) {
		if let Err(storage::ContractAbsentError) =
			storage::set_rent_allowance::<T>(&self.ctx.self_account, rent_allowance)
		{
			panic!(
				"`self_account` points to an alive contract within the `CallContext`;
					set_rent_allowance cannot return `Err`; qed"
			);
		}
	}

	fn rent_allowance(&self) -> BalanceOf<T> {
		storage::rent_allowance::<T>(&self.ctx.self_account)
			.unwrap_or_else(|_| <BalanceOf<T>>::max_value()) // Must never be triggered actually
	}

	fn block_number(&self) -> T::BlockNumber { self.block_number }

	fn max_value_size(&self) -> u32 {
		self.ctx.config.max_value_size
	}

	fn get_weight_price(&self, weight: Weight) -> BalanceOf<Self::T> {
		T::WeightPrice::convert(weight)
	}
}

fn deposit_event<T: Trait>(
	topics: Vec<T::Hash>,
	event: Event<T>,
) {
	<frame_system::Module<T>>::deposit_event_indexed(
		&*topics,
		<T as Trait>::Event::from(event).into(),
	)
}

/// These tests exercise the executive layer.
///
/// In these tests the VM/loader are mocked. Instead of dealing with wasm bytecode they use simple closures.
/// This allows you to tackle executive logic more thoroughly without writing a
/// wasm VM code.
#[cfg(test)]
mod tests {
	use super::{
		BalanceOf, Event, ExecResult, ExecutionContext, Ext, Loader,
		RawEvent, Vm, ReturnFlags, ExecError, ErrorOrigin
	};
	use crate::{
		gas::GasMeter, tests::{ExtBuilder, Test, MetaEvent},
		exec::ExecReturnValue, CodeHash, Config,
		gas::Gas,
		storage, Error
	};
	use crate::tests::test_utils::{place_contract, set_balance, get_balance};
	use sp_runtime::DispatchError;
	use assert_matches::assert_matches;
	use std::{cell::RefCell, collections::HashMap, marker::PhantomData, rc::Rc};

	const ALICE: u64 = 1;
	const BOB: u64 = 2;
	const CHARLIE: u64 = 3;

	const GAS_LIMIT: Gas = 10_000_000_000;

	fn events() -> Vec<Event<Test>> {
		<frame_system::Module<Test>>::events()
			.into_iter()
			.filter_map(|meta| match meta.event {
				MetaEvent::contracts(contract_event) => Some(contract_event),
				_ => None,
			})
			.collect()
	}

	struct MockCtx<'a> {
		ext: &'a mut dyn Ext<T = Test>,
		input_data: Vec<u8>,
		gas_meter: &'a mut GasMeter<Test>,
	}

	#[derive(Clone)]
	struct MockExecutable<'a>(Rc<dyn Fn(MockCtx) -> ExecResult + 'a>);

	impl<'a> MockExecutable<'a> {
		fn new(f: impl Fn(MockCtx) -> ExecResult + 'a) -> Self {
			MockExecutable(Rc::new(f))
		}
	}

	struct MockLoader<'a> {
		map: HashMap<CodeHash<Test>, MockExecutable<'a>>,
		counter: u64,
	}

	impl<'a> MockLoader<'a> {
		fn empty() -> Self {
			MockLoader {
				map: HashMap::new(),
				counter: 0,
			}
		}

		fn insert(&mut self, f: impl Fn(MockCtx) -> ExecResult + 'a) -> CodeHash<Test> {
			// Generate code hashes as monotonically increasing values.
			let code_hash = <Test as frame_system::Trait>::Hash::from_low_u64_be(self.counter);

			self.counter += 1;
			self.map.insert(code_hash, MockExecutable::new(f));
			code_hash
		}
	}

	struct MockVm<'a> {
		_marker: PhantomData<&'a ()>,
	}

	impl<'a> MockVm<'a> {
		fn new() -> Self {
			MockVm { _marker: PhantomData }
		}
	}

	impl<'a> Loader<Test> for MockLoader<'a> {
		type Executable = MockExecutable<'a>;

		fn load_init(&self, code_hash: &CodeHash<Test>) -> Result<Self::Executable, &'static str> {
			self.map
				.get(code_hash)
				.cloned()
				.ok_or_else(|| "code not found")
		}
		fn load_main(&self, code_hash: &CodeHash<Test>) -> Result<Self::Executable, &'static str> {
			self.map
				.get(code_hash)
				.cloned()
				.ok_or_else(|| "code not found")
		}
	}

	impl<'a> Vm<Test> for MockVm<'a> {
		type Executable = MockExecutable<'a>;

		fn execute<E: Ext<T = Test>>(
			&self,
			exec: &MockExecutable,
			mut ext: E,
			input_data: Vec<u8>,
			gas_meter: &mut GasMeter<Test>,
		) -> ExecResult {
			(exec.0)(MockCtx {
				ext: &mut ext,
				input_data,
				gas_meter,
			})
		}
	}

	fn exec_success() -> ExecResult {
		Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Vec::new() })
	}

	#[test]
	fn it_works() {
		let value = Default::default();
		let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
		let data = vec![];

		let vm = MockVm::new();

		let test_data = Rc::new(RefCell::new(vec![0usize]));

		let mut loader = MockLoader::empty();
		let exec_ch = loader.insert(|_ctx| {
			test_data.borrow_mut().push(1);
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			place_contract(&BOB, exec_ch);

			assert_matches!(
				ctx.call(BOB, value, &mut gas_meter, data),
				Ok(_)
			);
		});

		assert_eq!(&*test_data.borrow(), &vec![0, 1]);
	}

	#[test]
	fn transfer_works() {
		// This test verifies that a contract is able to transfer
		// some funds to another account.
		let origin = ALICE;
		let dest = BOB;

		let vm = MockVm::new();
		let loader = MockLoader::empty();

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			set_balance(&origin, 100);
			set_balance(&dest, 0);

			super::transfer(
				super::TransferCause::Call,
				super::TransactorKind::PlainAccount,
				&origin,
				&dest,
				55,
				&mut ctx,
			).unwrap();

			assert_eq!(get_balance(&origin), 45);
			assert_eq!(get_balance(&dest), 55);
		});
	}

	#[test]
	fn changes_are_reverted_on_failing_call() {
		// This test verifies that changes are reverted on a call which fails (or equally, returns
		// a non-zero status code).
		let origin = ALICE;
		let dest = BOB;

		let vm = MockVm::new();
		let mut loader = MockLoader::empty();
		let return_ch = loader.insert(
			|_| Ok(ExecReturnValue { flags: ReturnFlags::REVERT, data: Vec::new() })
		);

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			place_contract(&BOB, return_ch);
			set_balance(&origin, 100);
			set_balance(&dest, 0);

			let output = ctx.call(
				dest,
				55,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				vec![],
			).unwrap();

			assert!(!output.is_success());
			assert_eq!(get_balance(&origin), 100);
			assert_eq!(get_balance(&dest), 0);
		});
	}

	#[test]
	fn balance_too_low() {
		// This test verifies that a contract can't send value if it's
		// balance is too low.
		let origin = ALICE;
		let dest = BOB;

		let vm = MockVm::new();
		let loader = MockLoader::empty();

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			set_balance(&origin, 0);

			let result = super::transfer(
				super::TransferCause::Call,
				super::TransactorKind::PlainAccount,
				&origin,
				&dest,
				100,
				&mut ctx,
			);

			assert_eq!(
				result,
				Err(Error::<Test>::TransferFailed.into())
			);
			assert_eq!(get_balance(&origin), 0);
			assert_eq!(get_balance(&dest), 0);
		});
	}

	#[test]
	fn output_is_returned_on_success() {
		// Verifies that if a contract returns data with a successful exit status, this data
		// is returned from the execution context.
		let origin = ALICE;
		let dest = BOB;

		let vm = MockVm::new();
		let mut loader = MockLoader::empty();
		let return_ch = loader.insert(
			|_| Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: vec![1, 2, 3, 4] })
		);

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			place_contract(&BOB, return_ch);

			let result = ctx.call(
				dest,
				0,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				vec![],
			);

			let output = result.unwrap();
			assert!(output.is_success());
			assert_eq!(output.data, vec![1, 2, 3, 4]);
		});
	}

	#[test]
	fn output_is_returned_on_failure() {
		// Verifies that if a contract returns data with a failing exit status, this data
		// is returned from the execution context.
		let origin = ALICE;
		let dest = BOB;

		let vm = MockVm::new();
		let mut loader = MockLoader::empty();
		let return_ch = loader.insert(
			|_| Ok(ExecReturnValue { flags: ReturnFlags::REVERT, data: vec![1, 2, 3, 4] })
		);

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			place_contract(&BOB, return_ch);

			let result = ctx.call(
				dest,
				0,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				vec![],
			);

			let output = result.unwrap();
			assert!(!output.is_success());
			assert_eq!(output.data, vec![1, 2, 3, 4]);
		});
	}

	#[test]
	fn input_data_to_call() {
		let vm = MockVm::new();
		let mut loader = MockLoader::empty();
		let input_data_ch = loader.insert(|ctx| {
			assert_eq!(ctx.input_data, &[1, 2, 3, 4]);
			exec_success()
		});

		// This one tests passing the input data into a contract via call.
		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			place_contract(&BOB, input_data_ch);

			let result = ctx.call(
				BOB,
				0,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				vec![1, 2, 3, 4],
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn input_data_to_instantiate() {
		let vm = MockVm::new();
		let mut loader = MockLoader::empty();
		let input_data_ch = loader.insert(|ctx| {
			assert_eq!(ctx.input_data, &[1, 2, 3, 4]);
			exec_success()
		});

		// This one tests passing the input data into a contract via instantiate.
		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);

			set_balance(&ALICE, 100);

			let result = ctx.instantiate(
				cfg.subsistence_threshold(),
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&input_data_ch,
				vec![1, 2, 3, 4],
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn max_depth() {
		// This test verifies that when we reach the maximal depth creation of an
		// yet another context fails.
		let value = Default::default();
		let reached_bottom = RefCell::new(false);

		let vm = MockVm::new();
		let mut loader = MockLoader::empty();
		let recurse_ch = loader.insert(|ctx| {
			// Try to call into yourself.
			let r = ctx.ext.call(&BOB, 0, ctx.gas_meter, vec![]);

			let mut reached_bottom = reached_bottom.borrow_mut();
			if !*reached_bottom {
				// We are first time here, it means we just reached bottom.
				// Verify that we've got proper error and set `reached_bottom`.
				assert_eq!(
					r,
					Err(Error::<Test>::MaxCallDepthReached.into())
				);
				*reached_bottom = true;
			} else {
				// We just unwinding stack here.
				assert_matches!(r, Ok(_));
			}

			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			set_balance(&BOB, 1);
			place_contract(&BOB, recurse_ch);

			let result = ctx.call(
				BOB,
				value,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				vec![],
			);

			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn caller_returns_proper_values() {
		let origin = ALICE;
		let dest = BOB;

		let vm = MockVm::new();

		let witnessed_caller_bob = RefCell::new(None::<u64>);
		let witnessed_caller_charlie = RefCell::new(None::<u64>);

		let mut loader = MockLoader::empty();
		let bob_ch = loader.insert(|ctx| {
			// Record the caller for bob.
			*witnessed_caller_bob.borrow_mut() = Some(*ctx.ext.caller());

			// Call into CHARLIE contract.
			assert_matches!(
				ctx.ext.call(&CHARLIE, 0, ctx.gas_meter, vec![]),
				Ok(_)
			);
			exec_success()
		});
		let charlie_ch = loader.insert(|ctx| {
			// Record the caller for charlie.
			*witnessed_caller_charlie.borrow_mut() = Some(*ctx.ext.caller());
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();

			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			place_contract(&dest, bob_ch);
			place_contract(&CHARLIE, charlie_ch);

			let result = ctx.call(
				dest,
				0,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				vec![],
			);

			assert_matches!(result, Ok(_));
		});

		assert_eq!(&*witnessed_caller_bob.borrow(), &Some(origin));
		assert_eq!(&*witnessed_caller_charlie.borrow(), &Some(dest));
	}

	#[test]
	fn address_returns_proper_values() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let bob_ch = loader.insert(|ctx| {
			// Verify that address matches BOB.
			assert_eq!(*ctx.ext.address(), BOB);

			// Call into charlie contract.
			assert_matches!(
				ctx.ext.call(&CHARLIE, 0, ctx.gas_meter, vec![]),
				Ok(_)
			);
			exec_success()
		});
		let charlie_ch = loader.insert(|ctx| {
			assert_eq!(*ctx.ext.address(), CHARLIE);
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			place_contract(&BOB, bob_ch);
			place_contract(&CHARLIE, charlie_ch);

			let result = ctx.call(
				BOB,
				0,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				vec![],
			);

			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn refuse_instantiate_with_value_below_existential_deposit() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let dummy_ch = loader.insert(|_| exec_success());

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);

			assert_matches!(
				ctx.instantiate(
					0, // <- zero endowment
					&mut GasMeter::<Test>::new(GAS_LIMIT),
					&dummy_ch,
					vec![],
				),
				Err(_)
			);
		});
	}

	#[test]
	fn instantiation_work_with_success_output() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let dummy_ch = loader.insert(
			|_| Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: vec![80, 65, 83, 83] })
		);

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			set_balance(&ALICE, 1000);

			let instantiated_contract_address = assert_matches!(
				ctx.instantiate(
					100,
					&mut GasMeter::<Test>::new(GAS_LIMIT),
					&dummy_ch,
					vec![],
				),
				Ok((address, ref output)) if output.data == vec![80, 65, 83, 83] => address
			);

			// Check that the newly created account has the expected code hash and
			// there are instantiation event.
			assert_eq!(storage::code_hash::<Test>(&instantiated_contract_address).unwrap(), dummy_ch);
			assert_eq!(&events(), &[
				RawEvent::Instantiated(ALICE, instantiated_contract_address)
			]);
		});
	}

	#[test]
	fn instantiation_fails_with_failing_output() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let dummy_ch = loader.insert(
			|_| Ok(ExecReturnValue { flags: ReturnFlags::REVERT, data: vec![70, 65, 73, 76] })
		);

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			set_balance(&ALICE, 1000);

			let instantiated_contract_address = assert_matches!(
				ctx.instantiate(
					100,
					&mut GasMeter::<Test>::new(GAS_LIMIT),
					&dummy_ch,
					vec![],
				),
				Ok((address, ref output)) if output.data == vec![70, 65, 73, 76] => address
			);

			// Check that the account has not been created.
			assert!(storage::code_hash::<Test>(&instantiated_contract_address).is_err());
			assert!(events().is_empty());
		});
	}

	#[test]
	fn instantiation_from_contract() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let dummy_ch = loader.insert(|_| exec_success());
		let instantiated_contract_address = Rc::new(RefCell::new(None::<u64>));
		let instantiator_ch = loader.insert({
			let dummy_ch = dummy_ch.clone();
			let instantiated_contract_address = Rc::clone(&instantiated_contract_address);
			move |ctx| {
				// Instantiate a contract and save it's address in `instantiated_contract_address`.
				let (address, output) = ctx.ext.instantiate(
					&dummy_ch,
					Config::<Test>::subsistence_threshold_uncached(),
					ctx.gas_meter,
					vec![]
				).unwrap();

				*instantiated_contract_address.borrow_mut() = address.into();
				Ok(output)
			}
		});

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			set_balance(&ALICE, 1000);
			set_balance(&BOB, 100);
			place_contract(&BOB, instantiator_ch);

			assert_matches!(
				ctx.call(BOB, 20, &mut GasMeter::<Test>::new(GAS_LIMIT), vec![]),
				Ok(_)
			);

			let instantiated_contract_address = instantiated_contract_address.borrow().as_ref().unwrap().clone();

			// Check that the newly created account has the expected code hash and
			// there are instantiation event.
			assert_eq!(storage::code_hash::<Test>(&instantiated_contract_address).unwrap(), dummy_ch);
			assert_eq!(&events(), &[
				RawEvent::Instantiated(BOB, instantiated_contract_address)
			]);
		});
	}

	#[test]
	fn instantiation_traps() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let dummy_ch = loader.insert(
			|_| Err("It's a trap!".into())
		);
		let instantiator_ch = loader.insert({
			let dummy_ch = dummy_ch.clone();
			move |ctx| {
				// Instantiate a contract and save it's address in `instantiated_contract_address`.
				assert_matches!(
					ctx.ext.instantiate(
						&dummy_ch,
						15u64,
						ctx.gas_meter,
						vec![]
					),
					Err(ExecError {
						error: DispatchError::Other("It's a trap!"),
						origin: ErrorOrigin::Callee,
					})
				);

				exec_success()
			}
		});

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			set_balance(&ALICE, 1000);
			set_balance(&BOB, 100);
			place_contract(&BOB, instantiator_ch);

			assert_matches!(
				ctx.call(BOB, 20, &mut GasMeter::<Test>::new(GAS_LIMIT), vec![]),
				Ok(_)
			);

			// The contract wasn't instantiated so we don't expect to see an instantiation
			// event here.
			assert_eq!(&events(), &[]);
		});
	}

	#[test]
	fn termination_from_instantiate_fails() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();

		let terminate_ch = loader.insert(|ctx| {
			ctx.ext.terminate(&ALICE).unwrap();
			exec_success()
		});

		ExtBuilder::default()
			.existential_deposit(15)
			.build()
			.execute_with(|| {
				let cfg = Config::preload();
				let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
				set_balance(&ALICE, 1000);

				assert_eq!(
					ctx.instantiate(
						100,
						&mut GasMeter::<Test>::new(GAS_LIMIT),
						&terminate_ch,
						vec![],
					),
					Err(Error::<Test>::NewContractNotFunded.into())
				);

				assert_eq!(
					&events(),
					&[]
				);
			});
	}

	#[test]
	fn rent_allowance() {
		let vm = MockVm::new();
		let mut loader = MockLoader::empty();
		let rent_allowance_ch = loader.insert(|ctx| {
			assert_eq!(ctx.ext.rent_allowance(), <BalanceOf<Test>>::max_value());
			ctx.ext.set_rent_allowance(10);
			assert_eq!(ctx.ext.rent_allowance(), 10);
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			set_balance(&ALICE, 100);

			let result = ctx.instantiate(
				cfg.subsistence_threshold(),
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&rent_allowance_ch,
				vec![],
			);
			assert_matches!(result, Ok(_));
		});
	}
}
