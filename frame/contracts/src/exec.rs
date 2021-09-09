// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use crate::{
	gas::GasMeter, storage::Storage, AccountCounter, BalanceOf, CodeHash, Config, ContractInfo,
	ContractInfoOf, Error, Event, Pallet as Contracts, Schedule,
};
use frame_support::{
	dispatch::{DispatchError, DispatchResult, DispatchResultWithPostInfo, Dispatchable},
	ensure,
	storage::{with_transaction, TransactionOutcome},
	traits::{Contains, Currency, ExistenceRequirement, Get, OriginTrait, Randomness, Time},
	weights::Weight,
};
use frame_system::RawOrigin;
use pallet_contracts_primitives::ExecReturnValue;
use smallvec::{Array, SmallVec};
use sp_core::crypto::UncheckedFrom;
use sp_runtime::traits::{Convert, Saturating};
use sp_std::{marker::PhantomData, mem, prelude::*};

/// When fields are added to the [`ContractInfo`] that can change during execution this
/// variable needs to be set to true. This will also force changes to the
/// `in_memory_changes_not_discarded` test.
const CONTRACT_INFO_CAN_CHANGE: bool = false;

pub type AccountIdOf<T> = <T as frame_system::Config>::AccountId;
pub type MomentOf<T> = <<T as Config>::Time as Time>::Moment;
pub type SeedOf<T> = <T as frame_system::Config>::Hash;
pub type BlockNumberOf<T> = <T as frame_system::Config>::BlockNumber;
pub type StorageKey = [u8; 32];
pub type ExecResult = Result<ExecReturnValue, ExecError>;

/// A type that represents a topic of an event. At the moment a hash is used.
pub type TopicOf<T> = <T as frame_system::Config>::Hash;

/// Origin of the error.
///
/// Call or instantiate both called into other contracts and pass through errors happening
/// in those to the caller. This enum is for the caller to distinguish whether the error
/// happened during the execution of the callee or in the current execution context.
#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum ErrorOrigin {
	/// Caller error origin.
	///
	/// The error happened in the current exeuction context rather than in the one
	/// of the contract that is called into.
	Caller,
	/// The error happened during execution of the called contract.
	Callee,
}

/// Error returned by contract exection.
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct ExecError {
	/// The reason why the execution failed.
	pub error: DispatchError,
	/// Origin of the error.
	pub origin: ErrorOrigin,
}

impl<T: Into<DispatchError>> From<T> for ExecError {
	fn from(error: T) -> Self {
		Self { error: error.into(), origin: ErrorOrigin::Caller }
	}
}

/// An interface that provides access to the external environment in which the
/// smart-contract is executed.
///
/// This interface is specialized to an account of the executing code, so all
/// operations are implicitly performed on that account.
///
/// # Note
///
/// This trait is sealed and cannot be implemented by downstream crates.
pub trait Ext: sealing::Sealed {
	type T: Config;

	/// Call (possibly transferring some amount of funds) into the specified account.
	///
	/// Returns the original code size of the called contract.
	///
	/// # Return Value
	///
	/// Result<(ExecReturnValue, CodeSize), (ExecError, CodeSize)>
	fn call(
		&mut self,
		gas_limit: Weight,
		to: AccountIdOf<Self::T>,
		value: BalanceOf<Self::T>,
		input_data: Vec<u8>,
		allows_reentry: bool,
	) -> Result<ExecReturnValue, ExecError>;

	/// Instantiate a contract from the given code.
	///
	/// Returns the original code size of the called contract.
	/// The newly created account will be associated with `code`. `value` specifies the amount of
	/// value transferred from this to the newly created account (also known as endowment).
	///
	/// # Return Value
	///
	/// Result<(AccountId, ExecReturnValue, CodeSize), (ExecError, CodeSize)>
	fn instantiate(
		&mut self,
		gas_limit: Weight,
		code: CodeHash<Self::T>,
		value: BalanceOf<Self::T>,
		input_data: Vec<u8>,
		salt: &[u8],
	) -> Result<(AccountIdOf<Self::T>, ExecReturnValue), ExecError>;

	/// Transfer all funds to `beneficiary` and delete the contract.
	///
	/// Since this function removes the self contract eagerly, if succeeded, no further actions
	/// should be performed on this `Ext` instance.
	///
	/// This function will fail if the same contract is present on the contract
	/// call stack.
	fn terminate(&mut self, beneficiary: &AccountIdOf<Self::T>) -> Result<(), DispatchError>;

	/// Transfer some amount of funds into the specified account.
	fn transfer(&mut self, to: &AccountIdOf<Self::T>, value: BalanceOf<Self::T>) -> DispatchResult;

	/// Returns the storage entry of the executing account by the given `key`.
	///
	/// Returns `None` if the `key` wasn't previously set by `set_storage` or
	/// was deleted.
	fn get_storage(&mut self, key: &StorageKey) -> Option<Vec<u8>>;

	/// Sets the storage entry by the given key to the specified value. If `value` is `None` then
	/// the storage entry is deleted.
	fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>) -> DispatchResult;

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

	/// Returns the deposit required to instantiate a contract.
	fn contract_deposit(&self) -> BalanceOf<Self::T>;

	/// Returns a random number for the current block with the given subject.
	fn random(&self, subject: &[u8]) -> (SeedOf<Self::T>, BlockNumberOf<Self::T>);

	/// Deposit an event with the given topics.
	///
	/// There should not be any duplicates in `topics`.
	fn deposit_event(&mut self, topics: Vec<TopicOf<Self::T>>, data: Vec<u8>);

	/// Returns the current block number.
	fn block_number(&self) -> BlockNumberOf<Self::T>;

	/// Returns the maximum allowed size of a storage item.
	fn max_value_size(&self) -> u32;

	/// Returns the price for the specified amount of weight.
	fn get_weight_price(&self, weight: Weight) -> BalanceOf<Self::T>;

	/// Get a reference to the schedule used by the current call.
	fn schedule(&self) -> &Schedule<Self::T>;

	/// Get a mutable reference to the nested gas meter.
	fn gas_meter(&mut self) -> &mut GasMeter<Self::T>;

	/// Append a string to the debug buffer.
	///
	/// It is added as-is without any additional new line.
	///
	/// This is a no-op if debug message recording is disabled which is always the case
	/// when the code is executing on-chain.
	///
	/// Returns `true` if debug message recording is enabled. Otherwise `false` is returned.
	fn append_debug_buffer(&mut self, msg: &str) -> bool;

	/// Call some dispatchable and return the result.
	fn call_runtime(&self, call: <Self::T as Config>::Call) -> DispatchResultWithPostInfo;
}

/// Describes the different functions that can be exported by an [`Executable`].
#[derive(Clone, Copy, PartialEq)]
pub enum ExportedFunction {
	/// The constructor function which is executed on deployment of a contract.
	Constructor,
	/// The function which is executed when a contract is called.
	Call,
}

/// A trait that represents something that can be executed.
///
/// In the on-chain environment this would be represented by a wasm module. This trait exists in
/// order to be able to mock the wasm logic for testing.
pub trait Executable<T: Config>: Sized {
	/// Load the executable from storage.
	///
	/// # Note
	/// Charges size base load and instrumentation weight from the gas meter.
	fn from_storage(
		code_hash: CodeHash<T>,
		schedule: &Schedule<T>,
		gas_meter: &mut GasMeter<T>,
	) -> Result<Self, DispatchError>;

	/// Load the module from storage without re-instrumenting it.
	///
	/// A code module is re-instrumented on-load when it was originally instrumented with
	/// an older schedule. This skips this step for cases where the code storage is
	/// queried for purposes other than execution.
	///
	/// # Note
	///
	/// Does not charge from the gas meter. Do not call in contexts where this is important.
	fn from_storage_noinstr(code_hash: CodeHash<T>) -> Result<Self, DispatchError>;

	/// Increment the refcount by one. Fails if the code does not exist on-chain.
	///
	/// Returns the size of the original code.
	///
	/// # Note
	///
	/// Charges weight proportional to the code size from the gas meter.
	fn add_user(code_hash: CodeHash<T>, gas_meter: &mut GasMeter<T>) -> Result<(), DispatchError>;

	/// Decrement the refcount by one and remove the code when it drops to zero.
	///
	/// Returns the size of the original code.
	///
	/// # Note
	///
	/// Charges weight proportional to the code size from the gas meter
	fn remove_user(
		code_hash: CodeHash<T>,
		gas_meter: &mut GasMeter<T>,
	) -> Result<(), DispatchError>;

	/// Execute the specified exported function and return the result.
	///
	/// When the specified function is `Constructor` the executable is stored and its
	/// refcount incremented.
	///
	/// # Note
	///
	/// This functions expects to be executed in a storage transaction that rolls back
	/// all of its emitted storage changes.
	fn execute<E: Ext<T = T>>(
		self,
		ext: &mut E,
		function: &ExportedFunction,
		input_data: Vec<u8>,
	) -> ExecResult;

	/// The code hash of the executable.
	fn code_hash(&self) -> &CodeHash<T>;

	/// Size of the instrumented code in bytes.
	fn code_len(&self) -> u32;

	/// Sum of instrumented and pristine code len.
	fn aggregate_code_len(&self) -> u32;

	// The number of contracts using this executable.
	fn refcount(&self) -> u32;
}

/// The complete call stack of a contract execution.
///
/// The call stack is initiated by either a signed origin or one of the contract RPC calls.
/// This type implements `Ext` and by that exposes the business logic of contract execution to
/// the runtime module which interfaces with the contract (the wasm blob) itself.
pub struct Stack<'a, T: Config, E> {
	/// The account id of a plain account that initiated the call stack.
	///
	/// # Note
	///
	/// Please note that it is possible that the id belongs to a contract rather than a plain
	/// account when being called through one of the contract RPCs where the client can freely
	/// choose the origin. This usually makes no sense but is still possible.
	origin: T::AccountId,
	/// The cost schedule used when charging from the gas meter.
	schedule: &'a Schedule<T>,
	/// The gas meter where costs are charged to.
	gas_meter: &'a mut GasMeter<T>,
	/// The timestamp at the point of call stack instantiation.
	timestamp: MomentOf<T>,
	/// The block number at the time of call stack instantiation.
	block_number: T::BlockNumber,
	/// The account counter is cached here when accessed. It is written back when the call stack
	/// finishes executing.
	account_counter: Option<u64>,
	/// The actual call stack. One entry per nested contract called/instantiated.
	/// This does **not** include the [`Self::first_frame`].
	frames: SmallVec<T::CallStack>,
	/// Statically guarantee that each call stack has at least one frame.
	first_frame: Frame<T>,
	/// A text buffer used to output human readable information.
	///
	/// All the bytes added to this field should be valid UTF-8. The buffer has no defined
	/// structure and is intended to be shown to users as-is for debugging purposes.
	debug_message: Option<&'a mut Vec<u8>>,
	/// No executable is held by the struct but influences its behaviour.
	_phantom: PhantomData<E>,
}

/// Represents one entry in the call stack.
///
/// For each nested contract call or instantiate one frame is created. It holds specific
/// information for the said call and caches the in-storage `ContractInfo` data structure.
///
/// # Note
///
/// This is an internal data structure. It is exposed to the public for the sole reason
/// of specifying [`Config::CallStack`].
pub struct Frame<T: Config> {
	/// The account id of the executing contract.
	account_id: T::AccountId,
	/// The cached in-storage data of the contract.
	contract_info: CachedContract<T>,
	/// The amount of balance transferred by the caller as part of the call.
	value_transferred: BalanceOf<T>,
	/// Determines whether this is a call or instantiate frame.
	entry_point: ExportedFunction,
	/// The gas meter capped to the supplied gas limit.
	nested_meter: GasMeter<T>,
	/// If `false` the contract enabled its defense against reentrance attacks.
	allows_reentry: bool,
}

/// Parameter passed in when creating a new `Frame`.
///
/// It determines whether the new frame is for a call or an instantiate.
enum FrameArgs<'a, T: Config, E> {
	Call {
		/// The account id of the contract that is to be called.
		dest: T::AccountId,
		/// If `None` the contract info needs to be reloaded from storage.
		cached_info: Option<ContractInfo<T>>,
	},
	Instantiate {
		/// The contract or signed origin which instantiates the new contract.
		sender: T::AccountId,
		/// The seed that should be used to derive a new trie id for the contract.
		trie_seed: u64,
		/// The executable whose `deploy` function is run.
		executable: E,
		/// A salt used in the contract address deriviation of the new contract.
		salt: &'a [u8],
	},
}

/// Describes the different states of a contract as contained in a `Frame`.
enum CachedContract<T: Config> {
	/// The cached contract is up to date with the in-storage value.
	Cached(ContractInfo<T>),
	/// A recursive call into the same contract did write to the contract info.
	///
	/// In this case the cached contract is stale and needs to be reloaded from storage.
	Invalidated,
	/// The current contract executed `terminate` and removed the contract.
	///
	/// In this case a reload is neither allowed nor possible. Please note that recursive
	/// calls cannot remove a contract as this is checked and denied.
	Terminated,
}

impl<T: Config> Frame<T> {
	/// Return the `contract_info` of the current contract.
	fn contract_info(&mut self) -> &mut ContractInfo<T> {
		self.contract_info.get(&self.account_id)
	}

	/// Terminate and return the `contract_info` of the current contract.
	///
	/// # Note
	///
	/// Under no circumstances the contract is allowed to access the `contract_info` after
	/// a call to this function. This would constitute a programming error in the exec module.
	fn terminate(&mut self) -> ContractInfo<T> {
		self.contract_info.terminate(&self.account_id)
	}
}

/// Extract the contract info after loading it from storage.
///
/// This assumes that `load` was executed before calling this macro.
macro_rules! get_cached_or_panic_after_load {
	($c:expr) => {{
		if let CachedContract::Cached(contract) = $c {
			contract
		} else {
			panic!(
				"It is impossible to remove a contract that is on the call stack;\
				See implementations of terminate;\
				Therefore fetching a contract will never fail while using an account id
				that is currently active on the call stack;\
				qed"
			);
		}
	}};
}

impl<T: Config> CachedContract<T> {
	/// Load the `contract_info` from storage if necessary.
	fn load(&mut self, account_id: &T::AccountId) {
		if let CachedContract::Invalidated = self {
			let contract = <ContractInfoOf<T>>::get(&account_id);
			if let Some(contract) = contract {
				*self = CachedContract::Cached(contract);
			}
		}
	}

	/// Return the cached contract_info.
	fn get(&mut self, account_id: &T::AccountId) -> &mut ContractInfo<T> {
		self.load(account_id);
		get_cached_or_panic_after_load!(self)
	}

	/// Terminate and return the contract info.
	fn terminate(&mut self, account_id: &T::AccountId) -> ContractInfo<T> {
		self.load(account_id);
		get_cached_or_panic_after_load!(mem::replace(self, Self::Terminated))
	}
}

impl<'a, T, E> Stack<'a, T, E>
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
	E: Executable<T>,
{
	/// Create an run a new call stack by calling into `dest`.
	///
	/// # Note
	///
	/// `debug_message` should only ever be set to `Some` when executing as an RPC because
	/// it adds allocations and could be abused to drive the runtime into an OOM panic.
	///
	/// # Return Value
	///
	/// Result<(ExecReturnValue, CodeSize), (ExecError, CodeSize)>
	pub fn run_call(
		origin: T::AccountId,
		dest: T::AccountId,
		gas_meter: &'a mut GasMeter<T>,
		schedule: &'a Schedule<T>,
		value: BalanceOf<T>,
		input_data: Vec<u8>,
		debug_message: Option<&'a mut Vec<u8>>,
	) -> Result<ExecReturnValue, ExecError> {
		let (mut stack, executable) = Self::new(
			FrameArgs::Call { dest, cached_info: None },
			origin,
			gas_meter,
			schedule,
			value,
			debug_message,
		)?;
		stack.run(executable, input_data)
	}

	/// Create and run a new call stack by instantiating a new contract.
	///
	/// # Note
	///
	/// `debug_message` should only ever be set to `Some` when executing as an RPC because
	/// it adds allocations and could be abused to drive the runtime into an OOM panic.
	///
	/// # Return Value
	///
	/// Result<(NewContractAccountId, ExecReturnValue), ExecError)>
	pub fn run_instantiate(
		origin: T::AccountId,
		executable: E,
		gas_meter: &'a mut GasMeter<T>,
		schedule: &'a Schedule<T>,
		value: BalanceOf<T>,
		input_data: Vec<u8>,
		salt: &[u8],
		debug_message: Option<&'a mut Vec<u8>>,
	) -> Result<(T::AccountId, ExecReturnValue), ExecError> {
		let (mut stack, executable) = Self::new(
			FrameArgs::Instantiate {
				sender: origin.clone(),
				trie_seed: Self::initial_trie_seed(),
				executable,
				salt,
			},
			origin,
			gas_meter,
			schedule,
			value,
			debug_message,
		)?;
		let account_id = stack.top_frame().account_id.clone();
		stack.run(executable, input_data).map(|ret| (account_id, ret))
	}

	/// Create a new call stack.
	fn new(
		args: FrameArgs<T, E>,
		origin: T::AccountId,
		gas_meter: &'a mut GasMeter<T>,
		schedule: &'a Schedule<T>,
		value: BalanceOf<T>,
		debug_message: Option<&'a mut Vec<u8>>,
	) -> Result<(Self, E), ExecError> {
		let (first_frame, executable) = Self::new_frame(args, value, gas_meter, 0, &schedule)?;
		let stack = Self {
			origin,
			schedule,
			gas_meter,
			timestamp: T::Time::now(),
			block_number: <frame_system::Pallet<T>>::block_number(),
			account_counter: None,
			first_frame,
			frames: Default::default(),
			debug_message,
			_phantom: Default::default(),
		};

		Ok((stack, executable))
	}

	/// Construct a new frame.
	///
	/// This does not take `self` because when constructing the first frame `self` is
	/// not initialized, yet.
	fn new_frame(
		frame_args: FrameArgs<T, E>,
		value_transferred: BalanceOf<T>,
		gas_meter: &mut GasMeter<T>,
		gas_limit: Weight,
		schedule: &Schedule<T>,
	) -> Result<(Frame<T>, E), ExecError> {
		let (account_id, contract_info, executable, entry_point) = match frame_args {
			FrameArgs::Call { dest, cached_info } => {
				let contract = if let Some(contract) = cached_info {
					contract
				} else {
					<ContractInfoOf<T>>::get(&dest).ok_or(<Error<T>>::ContractNotFound)?
				};

				let executable = E::from_storage(contract.code_hash, schedule, gas_meter)?;

				(dest, contract, executable, ExportedFunction::Call)
			},
			FrameArgs::Instantiate { sender, trie_seed, executable, salt } => {
				let account_id =
					<Contracts<T>>::contract_address(&sender, executable.code_hash(), &salt);
				let trie_id = Storage::<T>::generate_trie_id(&account_id, trie_seed);
				let contract = Storage::<T>::new_contract(
					&account_id,
					trie_id,
					executable.code_hash().clone(),
				)?;
				(account_id, contract, executable, ExportedFunction::Constructor)
			},
		};

		let frame = Frame {
			value_transferred,
			contract_info: CachedContract::Cached(contract_info),
			account_id,
			entry_point,
			nested_meter: gas_meter.nested(gas_limit)?,
			allows_reentry: true,
		};

		Ok((frame, executable))
	}

	/// Create a subsequent nested frame.
	fn push_frame(
		&mut self,
		frame_args: FrameArgs<T, E>,
		value_transferred: BalanceOf<T>,
		gas_limit: Weight,
	) -> Result<E, ExecError> {
		if self.frames.len() == T::CallStack::size() {
			return Err(Error::<T>::MaxCallDepthReached.into())
		}

		if CONTRACT_INFO_CAN_CHANGE {
			// We need to make sure that changes made to the contract info are not discarded.
			// See the `in_memory_changes_not_discarded` test for more information.
			// We do not store on instantiate because we do not allow to call into a contract
			// from its own constructor.
			let frame = self.top_frame();
			if let (CachedContract::Cached(contract), ExportedFunction::Call) =
				(&frame.contract_info, frame.entry_point)
			{
				<ContractInfoOf<T>>::insert(frame.account_id.clone(), contract.clone());
			}
		}

		let nested_meter =
			&mut self.frames.last_mut().unwrap_or(&mut self.first_frame).nested_meter;
		let (frame, executable) =
			Self::new_frame(frame_args, value_transferred, nested_meter, gas_limit, self.schedule)?;
		self.frames.push(frame);
		Ok(executable)
	}

	/// Run the current (top) frame.
	///
	/// This can be either a call or an instantiate.
	fn run(&mut self, executable: E, input_data: Vec<u8>) -> Result<ExecReturnValue, ExecError> {
		let entry_point = self.top_frame().entry_point;
		let do_transaction = || {
			// Every call or instantiate also optionally transferres balance.
			self.initial_transfer()?;

			// Call into the wasm blob.
			let output = executable
				.execute(self, &entry_point, input_data)
				.map_err(|e| ExecError { error: e.error, origin: ErrorOrigin::Callee })?;

			// Additional work needs to be performed in case of an instantiation.
			if output.is_success() && entry_point == ExportedFunction::Constructor {
				let frame = self.top_frame_mut();
				let account_id = frame.account_id.clone();

				// It is not allowed to terminate a contract inside its constructor.
				if let CachedContract::Terminated = frame.contract_info {
					return Err(Error::<T>::TerminatedInConstructor.into())
				}

				// Deposit an instantiation event.
				deposit_event::<T>(vec![], Event::Instantiated(self.caller().clone(), account_id));
			}

			Ok(output)
		};

		// All changes performed by the contract are executed under a storage transaction.
		// This allows for roll back on error. Changes to the cached contract_info are
		// comitted or rolled back when popping the frame.
		let (success, output) = with_transaction(|| {
			let output = do_transaction();
			match &output {
				Ok(result) if result.is_success() => TransactionOutcome::Commit((true, output)),
				_ => TransactionOutcome::Rollback((false, output)),
			}
		});
		self.pop_frame(success);
		output
	}

	/// Remove the current (top) frame from the stack.
	///
	/// This is called after running the current frame. It commits cached values to storage
	/// and invalidates all stale references to it that might exist further down the call stack.
	fn pop_frame(&mut self, persist: bool) {
		// Revert the account counter in case of a failed instantiation.
		if !persist && self.top_frame().entry_point == ExportedFunction::Constructor {
			self.account_counter.as_mut().map(|c| *c = c.wrapping_sub(1));
		}

		// Pop the current frame from the stack and return it in case it needs to interact
		// with duplicates that might exist on the stack.
		// A `None` means that we are returning from the `first_frame`.
		let frame = self.frames.pop();

		if let Some(frame) = frame {
			let prev = self.top_frame_mut();
			let account_id = &frame.account_id;
			prev.nested_meter.absorb_nested(frame.nested_meter);
			// Only gas counter changes are persisted in case of a failure.
			if !persist {
				return
			}
			if let CachedContract::Cached(contract) = frame.contract_info {
				// optimization: Predecessor is the same contract.
				// We can just copy the contract into the predecessor without a storage write.
				// This is possible when there is no other contract in-between that could
				// trigger a rollback.
				if prev.account_id == *account_id {
					prev.contract_info = CachedContract::Cached(contract);
					return
				}

				// Predecessor is a different contract: We persist the info and invalidate the first
				// stale cache we find. This triggers a reload from storage on next use. We skip(1)
				// because that case is already handled by the optimization above. Only the first
				// cache needs to be invalidated because that one will invalidate the next cache
				// when it is popped from the stack.
				<ContractInfoOf<T>>::insert(account_id, contract);
				if let Some(c) = self.frames_mut().skip(1).find(|f| f.account_id == *account_id) {
					c.contract_info = CachedContract::Invalidated;
				}
			}
		} else {
			if let Some((msg, false)) = self.debug_message.as_ref().map(|m| (m, m.is_empty())) {
				log::debug!(
					target: "runtime::contracts",
					"Execution finished with debug buffer: {}",
					core::str::from_utf8(msg).unwrap_or("<Invalid UTF8>"),
				);
			}
			// Write back to the root gas meter.
			self.gas_meter.absorb_nested(mem::take(&mut self.first_frame.nested_meter));
			// Only gas counter changes are persisted in case of a failure.
			if !persist {
				return
			}
			if let CachedContract::Cached(contract) = &self.first_frame.contract_info {
				<ContractInfoOf<T>>::insert(&self.first_frame.account_id, contract.clone());
			}
			if let Some(counter) = self.account_counter {
				<AccountCounter<T>>::set(counter);
			}
		}
	}

	/// Transfer some funds from `from` to `to`.
	///
	/// We only allow allow for draining all funds of the sender if `allow_death` is
	/// is specified as `true`. Otherwise, any transfer that would bring the sender below the
	/// subsistence threshold (for contracts) or the existential deposit (for plain accounts)
	/// results in an error.
	fn transfer(
		sender_is_contract: bool,
		allow_death: bool,
		from: &T::AccountId,
		to: &T::AccountId,
		value: BalanceOf<T>,
	) -> DispatchResult {
		if value == 0u32.into() {
			return Ok(())
		}

		let existence_requirement = match (allow_death, sender_is_contract) {
			(true, _) => ExistenceRequirement::AllowDeath,
			(false, true) => {
				ensure!(
					T::Currency::total_balance(from).saturating_sub(value) >=
						Contracts::<T>::subsistence_threshold(),
					Error::<T>::BelowSubsistenceThreshold,
				);
				ExistenceRequirement::KeepAlive
			},
			(false, false) => ExistenceRequirement::KeepAlive,
		};

		T::Currency::transfer(from, to, value, existence_requirement)
			.map_err(|_| Error::<T>::TransferFailed)?;

		Ok(())
	}

	// The transfer as performed by a call or instantiate.
	fn initial_transfer(&self) -> DispatchResult {
		let frame = self.top_frame();
		let value = frame.value_transferred;
		let subsistence_threshold = <Contracts<T>>::subsistence_threshold();

		// If the value transferred to a new contract is less than the subsistence threshold
		// we can error out early. This avoids executing the constructor in cases where
		// we already know that the contract has too little balance.
		if frame.entry_point == ExportedFunction::Constructor && value < subsistence_threshold {
			return Err(<Error<T>>::NewContractNotFunded.into())
		}

		Self::transfer(self.caller_is_origin(), false, self.caller(), &frame.account_id, value)
	}

	/// Wether the caller is the initiator of the call stack.
	fn caller_is_origin(&self) -> bool {
		!self.frames.is_empty()
	}

	/// Reference to the current (top) frame.
	fn top_frame(&self) -> &Frame<T> {
		self.frames.last().unwrap_or(&self.first_frame)
	}

	/// Mutable reference to the current (top) frame.
	fn top_frame_mut(&mut self) -> &mut Frame<T> {
		self.frames.last_mut().unwrap_or(&mut self.first_frame)
	}

	/// Iterator over all frames.
	///
	/// The iterator starts with the top frame and ends with the root frame.
	fn frames(&self) -> impl Iterator<Item = &Frame<T>> {
		sp_std::iter::once(&self.first_frame).chain(&self.frames).rev()
	}

	/// Same as `frames` but with a mutable reference as iterator item.
	fn frames_mut(&mut self) -> impl Iterator<Item = &mut Frame<T>> {
		sp_std::iter::once(&mut self.first_frame).chain(&mut self.frames).rev()
	}

	/// Returns whether the current contract is on the stack multiple times.
	fn is_recursive(&self) -> bool {
		let account_id = &self.top_frame().account_id;
		self.frames().skip(1).any(|f| &f.account_id == account_id)
	}

	/// Returns whether the specified contract allows to be reentered right now.
	fn allows_reentry(&self, id: &AccountIdOf<T>) -> bool {
		!self.frames().any(|f| &f.account_id == id && !f.allows_reentry)
	}

	/// Increments the cached account id and returns the value to be used for the trie_id.
	fn next_trie_seed(&mut self) -> u64 {
		let next = if let Some(current) = self.account_counter {
			current + 1
		} else {
			Self::initial_trie_seed()
		};
		self.account_counter = Some(next);
		next
	}

	/// The account seed to be used to instantiate the account counter cache.
	fn initial_trie_seed() -> u64 {
		<AccountCounter<T>>::get().wrapping_add(1)
	}
}

impl<'a, T, E> Ext for Stack<'a, T, E>
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
	E: Executable<T>,
{
	type T = T;

	fn call(
		&mut self,
		gas_limit: Weight,
		to: T::AccountId,
		value: BalanceOf<T>,
		input_data: Vec<u8>,
		allows_reentry: bool,
	) -> Result<ExecReturnValue, ExecError> {
		// Before pushing the new frame: Protect the caller contract against reentrancy attacks.
		// It is important to do this before calling `allows_reentry` so that a direct recursion
		// is caught by it.
		self.top_frame_mut().allows_reentry = allows_reentry;

		let try_call = || {
			if !self.allows_reentry(&to) {
				return Err(<Error<T>>::ReentranceDenied.into())
			}
			// We ignore instantiate frames in our search for a cached contract.
			// Otherwise it would be possible to recursively call a contract from its own
			// constructor: We disallow calling not fully constructed contracts.
			let cached_info = self
				.frames()
				.find(|f| f.entry_point == ExportedFunction::Call && f.account_id == to)
				.and_then(|f| match &f.contract_info {
					CachedContract::Cached(contract) => Some(contract.clone()),
					_ => None,
				});
			let executable =
				self.push_frame(FrameArgs::Call { dest: to, cached_info }, value, gas_limit)?;
			self.run(executable, input_data)
		};

		// We need to make sure to reset `allows_reentry` even on failure.
		let result = try_call();

		// Protection is on a per call basis.
		self.top_frame_mut().allows_reentry = true;

		result
	}

	fn instantiate(
		&mut self,
		gas_limit: Weight,
		code_hash: CodeHash<T>,
		endowment: BalanceOf<T>,
		input_data: Vec<u8>,
		salt: &[u8],
	) -> Result<(AccountIdOf<T>, ExecReturnValue), ExecError> {
		let executable = E::from_storage(code_hash, &self.schedule, self.gas_meter())?;
		let trie_seed = self.next_trie_seed();
		let executable = self.push_frame(
			FrameArgs::Instantiate {
				sender: self.top_frame().account_id.clone(),
				trie_seed,
				executable,
				salt,
			},
			endowment,
			gas_limit,
		)?;
		let account_id = self.top_frame().account_id.clone();
		self.run(executable, input_data).map(|ret| (account_id, ret))
	}

	fn terminate(&mut self, beneficiary: &AccountIdOf<Self::T>) -> Result<(), DispatchError> {
		if self.is_recursive() {
			return Err(Error::<T>::TerminatedWhileReentrant.into())
		}
		let frame = self.top_frame_mut();
		let info = frame.terminate();
		Storage::<T>::queue_trie_for_deletion(&info)?;
		<Stack<'a, T, E>>::transfer(
			true,
			true,
			&frame.account_id,
			beneficiary,
			T::Currency::free_balance(&frame.account_id),
		)?;
		ContractInfoOf::<T>::remove(&frame.account_id);
		E::remove_user(info.code_hash, &mut frame.nested_meter)?;
		Contracts::<T>::deposit_event(Event::Terminated(
			frame.account_id.clone(),
			beneficiary.clone(),
		));
		Ok(())
	}

	fn transfer(&mut self, to: &T::AccountId, value: BalanceOf<T>) -> DispatchResult {
		Self::transfer(true, false, &self.top_frame().account_id, to, value)
	}

	fn get_storage(&mut self, key: &StorageKey) -> Option<Vec<u8>> {
		Storage::<T>::read(&self.top_frame_mut().contract_info().trie_id, key)
	}

	fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>) -> DispatchResult {
		let frame = self.top_frame_mut();
		Storage::<T>::write(frame.contract_info(), &key, value)
	}

	fn address(&self) -> &T::AccountId {
		&self.top_frame().account_id
	}

	fn caller(&self) -> &T::AccountId {
		self.frames().nth(1).map(|f| &f.account_id).unwrap_or(&self.origin)
	}

	fn balance(&self) -> BalanceOf<T> {
		T::Currency::free_balance(&self.top_frame().account_id)
	}

	fn value_transferred(&self) -> BalanceOf<T> {
		self.top_frame().value_transferred
	}

	fn random(&self, subject: &[u8]) -> (SeedOf<T>, BlockNumberOf<T>) {
		T::Randomness::random(subject)
	}

	fn now(&self) -> &MomentOf<T> {
		&self.timestamp
	}

	fn minimum_balance(&self) -> BalanceOf<T> {
		T::Currency::minimum_balance()
	}

	fn contract_deposit(&self) -> BalanceOf<T> {
		T::ContractDeposit::get()
	}

	fn deposit_event(&mut self, topics: Vec<T::Hash>, data: Vec<u8>) {
		deposit_event::<Self::T>(
			topics,
			Event::ContractEmitted(self.top_frame().account_id.clone(), data),
		);
	}

	fn block_number(&self) -> T::BlockNumber {
		self.block_number
	}

	fn max_value_size(&self) -> u32 {
		T::Schedule::get().limits.payload_len
	}

	fn get_weight_price(&self, weight: Weight) -> BalanceOf<Self::T> {
		T::WeightPrice::convert(weight)
	}

	fn schedule(&self) -> &Schedule<Self::T> {
		&self.schedule
	}

	fn gas_meter(&mut self) -> &mut GasMeter<Self::T> {
		&mut self.top_frame_mut().nested_meter
	}

	fn append_debug_buffer(&mut self, msg: &str) -> bool {
		if let Some(buffer) = &mut self.debug_message {
			if !msg.is_empty() {
				buffer.extend(msg.as_bytes());
			}
			true
		} else {
			false
		}
	}

	fn call_runtime(&self, call: <Self::T as Config>::Call) -> DispatchResultWithPostInfo {
		let mut origin: T::Origin = RawOrigin::Signed(self.address().clone()).into();
		origin.add_filter(T::CallFilter::contains);
		call.dispatch(origin)
	}
}

fn deposit_event<T: Config>(topics: Vec<T::Hash>, event: Event<T>) {
	<frame_system::Pallet<T>>::deposit_event_indexed(
		&*topics,
		<T as Config>::Event::from(event).into(),
	)
}

mod sealing {
	use super::*;

	pub trait Sealed {}

	impl<'a, T: Config, E> Sealed for Stack<'a, T, E> {}

	#[cfg(test)]
	impl Sealed for crate::wasm::MockExt {}

	#[cfg(test)]
	impl Sealed for &mut crate::wasm::MockExt {}
}

/// These tests exercise the executive layer.
///
/// In these tests the VM/loader are mocked. Instead of dealing with wasm bytecode they use simple
/// closures. This allows you to tackle executive logic more thoroughly without writing a
/// wasm VM code.
#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		exec::ExportedFunction::*,
		gas::GasMeter,
		storage::Storage,
		tests::{
			test_utils::{get_balance, place_contract, set_balance},
			Call, Event as MetaEvent, ExtBuilder, Test, TestFilter, ALICE, BOB, CHARLIE,
		},
		Error, Weight,
	};
	use assert_matches::assert_matches;
	use codec::{Decode, Encode};
	use frame_support::{assert_err, assert_ok};
	use frame_system::{EventRecord, Phase};
	use pallet_contracts_primitives::ReturnFlags;
	use pretty_assertions::assert_eq;
	use sp_core::Bytes;
	use sp_runtime::{
		traits::{BadOrigin, Hash},
		DispatchError,
	};
	use std::{cell::RefCell, collections::HashMap, rc::Rc};

	type System = frame_system::Pallet<Test>;

	type MockStack<'a> = Stack<'a, Test, MockExecutable>;

	const GAS_LIMIT: Weight = 10_000_000_000;

	thread_local! {
		static LOADER: RefCell<MockLoader> = RefCell::new(MockLoader::default());
	}

	fn events() -> Vec<Event<Test>> {
		System::events()
			.into_iter()
			.filter_map(|meta| match meta.event {
				MetaEvent::Contracts(contract_event) => Some(contract_event),
				_ => None,
			})
			.collect()
	}

	struct MockCtx<'a> {
		ext: &'a mut dyn Ext<T = Test>,
		input_data: Vec<u8>,
	}

	#[derive(Clone)]
	struct MockExecutable {
		func: Rc<dyn Fn(MockCtx, &Self) -> ExecResult + 'static>,
		func_type: ExportedFunction,
		code_hash: CodeHash<Test>,
		refcount: u64,
	}

	#[derive(Default)]
	struct MockLoader {
		map: HashMap<CodeHash<Test>, MockExecutable>,
		counter: u64,
	}

	impl MockLoader {
		fn insert(
			func_type: ExportedFunction,
			f: impl Fn(MockCtx, &MockExecutable) -> ExecResult + 'static,
		) -> CodeHash<Test> {
			LOADER.with(|loader| {
				let mut loader = loader.borrow_mut();
				// Generate code hashes as monotonically increasing values.
				let hash = <Test as frame_system::Config>::Hash::from_low_u64_be(loader.counter);
				loader.counter += 1;
				loader.map.insert(
					hash,
					MockExecutable {
						func: Rc::new(f),
						func_type,
						code_hash: hash.clone(),
						refcount: 1,
					},
				);
				hash
			})
		}

		fn increment_refcount(code_hash: CodeHash<Test>) {
			LOADER.with(|loader| {
				let mut loader = loader.borrow_mut();
				loader
					.map
					.entry(code_hash)
					.and_modify(|executable| executable.refcount += 1)
					.or_insert_with(|| panic!("code_hash does not exist"));
			});
		}

		fn decrement_refcount(code_hash: CodeHash<Test>) {
			use std::collections::hash_map::Entry::Occupied;
			LOADER.with(|loader| {
				let mut loader = loader.borrow_mut();
				let mut entry = match loader.map.entry(code_hash) {
					Occupied(e) => e,
					_ => panic!("code_hash does not exist"),
				};
				let refcount = &mut entry.get_mut().refcount;
				*refcount -= 1;
				if *refcount == 0 {
					entry.remove();
				}
			});
		}
	}

	impl Executable<Test> for MockExecutable {
		fn from_storage(
			code_hash: CodeHash<Test>,
			_schedule: &Schedule<Test>,
			_gas_meter: &mut GasMeter<Test>,
		) -> Result<Self, DispatchError> {
			Self::from_storage_noinstr(code_hash)
		}

		fn from_storage_noinstr(code_hash: CodeHash<Test>) -> Result<Self, DispatchError> {
			LOADER.with(|loader| {
				loader
					.borrow_mut()
					.map
					.get(&code_hash)
					.cloned()
					.ok_or(Error::<Test>::CodeNotFound.into())
			})
		}

		fn add_user(
			code_hash: CodeHash<Test>,
			_: &mut GasMeter<Test>,
		) -> Result<(), DispatchError> {
			MockLoader::increment_refcount(code_hash);
			Ok(())
		}

		fn remove_user(
			code_hash: CodeHash<Test>,
			_: &mut GasMeter<Test>,
		) -> Result<(), DispatchError> {
			MockLoader::decrement_refcount(code_hash);
			Ok(())
		}

		fn execute<E: Ext<T = Test>>(
			self,
			ext: &mut E,
			function: &ExportedFunction,
			input_data: Vec<u8>,
		) -> ExecResult {
			if let &Constructor = function {
				MockLoader::increment_refcount(self.code_hash);
			}
			if function == &self.func_type {
				(self.func)(MockCtx { ext, input_data }, &self)
			} else {
				exec_success()
			}
		}

		fn code_hash(&self) -> &CodeHash<Test> {
			&self.code_hash
		}

		fn code_len(&self) -> u32 {
			0
		}

		fn aggregate_code_len(&self) -> u32 {
			0
		}

		fn refcount(&self) -> u32 {
			self.refcount as u32
		}
	}

	fn exec_success() -> ExecResult {
		Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Bytes(Vec::new()) })
	}

	fn exec_trapped() -> ExecResult {
		Err(ExecError { error: <Error<Test>>::ContractTrapped.into(), origin: ErrorOrigin::Callee })
	}

	#[test]
	fn it_works() {
		thread_local! {
			static TEST_DATA: RefCell<Vec<usize>> = RefCell::new(vec![0]);
		}

		let value = Default::default();
		let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
		let exec_ch = MockLoader::insert(Call, |_ctx, _executable| {
			TEST_DATA.with(|data| data.borrow_mut().push(1));
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, exec_ch);

			assert_matches!(
				MockStack::run_call(ALICE, BOB, &mut gas_meter, &schedule, value, vec![], None,),
				Ok(_)
			);
		});

		TEST_DATA.with(|data| assert_eq!(*data.borrow(), vec![0, 1]));
	}

	#[test]
	fn transfer_works() {
		// This test verifies that a contract is able to transfer
		// some funds to another account.
		let origin = ALICE;
		let dest = BOB;

		ExtBuilder::default().build().execute_with(|| {
			set_balance(&origin, 100);
			set_balance(&dest, 0);

			MockStack::transfer(true, false, &origin, &dest, 55).unwrap();

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

		let return_ch = MockLoader::insert(Call, |_, _| {
			Ok(ExecReturnValue { flags: ReturnFlags::REVERT, data: Bytes(Vec::new()) })
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&dest, return_ch);
			set_balance(&origin, 100);
			let balance = get_balance(&dest);

			let output = MockStack::run_call(
				origin.clone(),
				dest.clone(),
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&schedule,
				55,
				vec![],
				None,
			)
			.unwrap();

			assert!(!output.is_success());
			assert_eq!(get_balance(&origin), 100);
			assert_eq!(get_balance(&dest), balance);
		});
	}

	#[test]
	fn balance_too_low() {
		// This test verifies that a contract can't send value if it's
		// balance is too low.
		let origin = ALICE;
		let dest = BOB;

		ExtBuilder::default().build().execute_with(|| {
			set_balance(&origin, 0);

			let result = MockStack::transfer(false, false, &origin, &dest, 100);

			assert_eq!(result, Err(Error::<Test>::TransferFailed.into()));
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
		let return_ch = MockLoader::insert(Call, |_, _| {
			Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Bytes(vec![1, 2, 3, 4]) })
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, return_ch);

			let result = MockStack::run_call(
				origin,
				dest,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&schedule,
				0,
				vec![],
				None,
			);

			let output = result.unwrap();
			assert!(output.is_success());
			assert_eq!(output.data, Bytes(vec![1, 2, 3, 4]));
		});
	}

	#[test]
	fn output_is_returned_on_failure() {
		// Verifies that if a contract returns data with a failing exit status, this data
		// is returned from the execution context.
		let origin = ALICE;
		let dest = BOB;
		let return_ch = MockLoader::insert(Call, |_, _| {
			Ok(ExecReturnValue { flags: ReturnFlags::REVERT, data: Bytes(vec![1, 2, 3, 4]) })
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, return_ch);

			let result = MockStack::run_call(
				origin,
				dest,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&schedule,
				0,
				vec![],
				None,
			);

			let output = result.unwrap();
			assert!(!output.is_success());
			assert_eq!(output.data, Bytes(vec![1, 2, 3, 4]));
		});
	}

	#[test]
	fn input_data_to_call() {
		let input_data_ch = MockLoader::insert(Call, |ctx, _| {
			assert_eq!(ctx.input_data, &[1, 2, 3, 4]);
			exec_success()
		});

		// This one tests passing the input data into a contract via call.
		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, input_data_ch);

			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&schedule,
				0,
				vec![1, 2, 3, 4],
				None,
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn input_data_to_instantiate() {
		let input_data_ch = MockLoader::insert(Constructor, |ctx, _| {
			assert_eq!(ctx.input_data, &[1, 2, 3, 4]);
			exec_success()
		});

		// This one tests passing the input data into a contract via instantiate.
		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			let subsistence = Contracts::<Test>::subsistence_threshold();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			let executable =
				MockExecutable::from_storage(input_data_ch, &schedule, &mut gas_meter).unwrap();

			set_balance(&ALICE, subsistence * 10);

			let result = MockStack::run_instantiate(
				ALICE,
				executable,
				&mut gas_meter,
				&schedule,
				subsistence * 3,
				vec![1, 2, 3, 4],
				&[],
				None,
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn max_depth() {
		// This test verifies that when we reach the maximal depth creation of an
		// yet another context fails.
		thread_local! {
			static REACHED_BOTTOM: RefCell<bool> = RefCell::new(false);
		}
		let value = Default::default();
		let recurse_ch = MockLoader::insert(Call, |ctx, _| {
			// Try to call into yourself.
			let r = ctx.ext.call(0, BOB, 0, vec![], true);

			REACHED_BOTTOM.with(|reached_bottom| {
				let mut reached_bottom = reached_bottom.borrow_mut();
				if !*reached_bottom {
					// We are first time here, it means we just reached bottom.
					// Verify that we've got proper error and set `reached_bottom`.
					assert_eq!(r, Err(Error::<Test>::MaxCallDepthReached.into()));
					*reached_bottom = true;
				} else {
					// We just unwinding stack here.
					assert_matches!(r, Ok(_));
				}
			});

			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			set_balance(&BOB, 1);
			place_contract(&BOB, recurse_ch);

			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&schedule,
				value,
				vec![],
				None,
			);

			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn caller_returns_proper_values() {
		let origin = ALICE;
		let dest = BOB;

		thread_local! {
			static WITNESSED_CALLER_BOB: RefCell<Option<AccountIdOf<Test>>> = RefCell::new(None);
			static WITNESSED_CALLER_CHARLIE: RefCell<Option<AccountIdOf<Test>>> = RefCell::new(None);
		}

		let bob_ch = MockLoader::insert(Call, |ctx, _| {
			// Record the caller for bob.
			WITNESSED_CALLER_BOB
				.with(|caller| *caller.borrow_mut() = Some(ctx.ext.caller().clone()));

			// Call into CHARLIE contract.
			assert_matches!(ctx.ext.call(0, CHARLIE, 0, vec![], true), Ok(_));
			exec_success()
		});
		let charlie_ch = MockLoader::insert(Call, |ctx, _| {
			// Record the caller for charlie.
			WITNESSED_CALLER_CHARLIE
				.with(|caller| *caller.borrow_mut() = Some(ctx.ext.caller().clone()));
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&dest, bob_ch);
			place_contract(&CHARLIE, charlie_ch);

			let result = MockStack::run_call(
				origin.clone(),
				dest.clone(),
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&schedule,
				0,
				vec![],
				None,
			);

			assert_matches!(result, Ok(_));
		});

		WITNESSED_CALLER_BOB.with(|caller| assert_eq!(*caller.borrow(), Some(origin)));
		WITNESSED_CALLER_CHARLIE.with(|caller| assert_eq!(*caller.borrow(), Some(dest)));
	}

	#[test]
	fn address_returns_proper_values() {
		let bob_ch = MockLoader::insert(Call, |ctx, _| {
			// Verify that address matches BOB.
			assert_eq!(*ctx.ext.address(), BOB);

			// Call into charlie contract.
			assert_matches!(ctx.ext.call(0, CHARLIE, 0, vec![], true), Ok(_));
			exec_success()
		});
		let charlie_ch = MockLoader::insert(Call, |ctx, _| {
			assert_eq!(*ctx.ext.address(), CHARLIE);
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, bob_ch);
			place_contract(&CHARLIE, charlie_ch);

			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&schedule,
				0,
				vec![],
				None,
			);

			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn refuse_instantiate_with_value_below_existential_deposit() {
		let dummy_ch = MockLoader::insert(Constructor, |_, _| exec_success());

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			let executable =
				MockExecutable::from_storage(dummy_ch, &schedule, &mut gas_meter).unwrap();

			assert_matches!(
				MockStack::run_instantiate(
					ALICE,
					executable,
					&mut gas_meter,
					&schedule,
					0, // <- zero endowment
					vec![],
					&[],
					None,
				),
				Err(_)
			);
		});
	}

	#[test]
	fn instantiation_work_with_success_output() {
		let dummy_ch = MockLoader::insert(Constructor, |_, _| {
			Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Bytes(vec![80, 65, 83, 83]) })
		});

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			let executable =
				MockExecutable::from_storage(dummy_ch, &schedule, &mut gas_meter).unwrap();
			set_balance(&ALICE, 1000);

			let instantiated_contract_address = assert_matches!(
				MockStack::run_instantiate(
					ALICE,
					executable,
					&mut gas_meter,
					&schedule,
					100,
					vec![],
					&[],
					None,
				),
				Ok((address, ref output)) if output.data == Bytes(vec![80, 65, 83, 83]) => address
			);

			// Check that the newly created account has the expected code hash and
			// there are instantiation event.
			assert_eq!(
				Storage::<Test>::code_hash(&instantiated_contract_address).unwrap(),
				dummy_ch
			);
			assert_eq!(&events(), &[Event::Instantiated(ALICE, instantiated_contract_address)]);
		});
	}

	#[test]
	fn instantiation_fails_with_failing_output() {
		let dummy_ch = MockLoader::insert(Constructor, |_, _| {
			Ok(ExecReturnValue { flags: ReturnFlags::REVERT, data: Bytes(vec![70, 65, 73, 76]) })
		});

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			let executable =
				MockExecutable::from_storage(dummy_ch, &schedule, &mut gas_meter).unwrap();
			set_balance(&ALICE, 1000);

			let instantiated_contract_address = assert_matches!(
				MockStack::run_instantiate(
					ALICE,
					executable,
					&mut gas_meter,
					&schedule,
					100,
					vec![],
					&[],
					None,
				),
				Ok((address, ref output)) if output.data == Bytes(vec![70, 65, 73, 76]) => address
			);

			// Check that the account has not been created.
			assert!(Storage::<Test>::code_hash(&instantiated_contract_address).is_none());
			assert!(events().is_empty());
		});
	}

	#[test]
	fn instantiation_from_contract() {
		let dummy_ch = MockLoader::insert(Call, |_, _| exec_success());
		let instantiated_contract_address = Rc::new(RefCell::new(None::<AccountIdOf<Test>>));
		let instantiator_ch = MockLoader::insert(Call, {
			let dummy_ch = dummy_ch.clone();
			let instantiated_contract_address = Rc::clone(&instantiated_contract_address);
			move |ctx, _| {
				// Instantiate a contract and save it's address in `instantiated_contract_address`.
				let (address, output) = ctx
					.ext
					.instantiate(
						0,
						dummy_ch,
						Contracts::<Test>::subsistence_threshold() * 3,
						vec![],
						&[48, 49, 50],
					)
					.unwrap();

				*instantiated_contract_address.borrow_mut() = address.into();
				Ok(output)
			}
		});

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			set_balance(&ALICE, Contracts::<Test>::subsistence_threshold() * 100);
			place_contract(&BOB, instantiator_ch);

			assert_matches!(
				MockStack::run_call(
					ALICE,
					BOB,
					&mut GasMeter::<Test>::new(GAS_LIMIT),
					&schedule,
					20,
					vec![],
					None,
				),
				Ok(_)
			);

			let instantiated_contract_address =
				instantiated_contract_address.borrow().as_ref().unwrap().clone();

			// Check that the newly created account has the expected code hash and
			// there are instantiation event.
			assert_eq!(
				Storage::<Test>::code_hash(&instantiated_contract_address).unwrap(),
				dummy_ch
			);
			assert_eq!(&events(), &[Event::Instantiated(BOB, instantiated_contract_address)]);
		});
	}

	#[test]
	fn instantiation_traps() {
		let dummy_ch = MockLoader::insert(Constructor, |_, _| Err("It's a trap!".into()));
		let instantiator_ch = MockLoader::insert(Call, {
			let dummy_ch = dummy_ch.clone();
			move |ctx, _| {
				// Instantiate a contract and save it's address in `instantiated_contract_address`.
				assert_matches!(
					ctx.ext.instantiate(
						0,
						dummy_ch,
						Contracts::<Test>::subsistence_threshold(),
						vec![],
						&[],
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
			let schedule = <Test as Config>::Schedule::get();
			set_balance(&ALICE, 1000);
			set_balance(&BOB, 100);
			place_contract(&BOB, instantiator_ch);

			assert_matches!(
				MockStack::run_call(
					ALICE,
					BOB,
					&mut GasMeter::<Test>::new(GAS_LIMIT),
					&schedule,
					20,
					vec![],
					None,
				),
				Ok(_)
			);

			// The contract wasn't instantiated so we don't expect to see an instantiation
			// event here.
			assert_eq!(&events(), &[]);
		});
	}

	#[test]
	fn termination_from_instantiate_fails() {
		let terminate_ch = MockLoader::insert(Constructor, |ctx, _| {
			ctx.ext.terminate(&ALICE).unwrap();
			exec_success()
		});

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			let executable =
				MockExecutable::from_storage(terminate_ch, &schedule, &mut gas_meter).unwrap();
			set_balance(&ALICE, 1000);

			assert_eq!(
				MockStack::run_instantiate(
					ALICE,
					executable,
					&mut gas_meter,
					&schedule,
					100,
					vec![],
					&[],
					None,
				),
				Err(Error::<Test>::TerminatedInConstructor.into())
			);

			assert_eq!(&events(), &[]);
		});
	}

	#[test]
	fn in_memory_changes_not_discarded() {
		// Remove this assert and fill out the "DO" stubs once fields are added to the
		// contract info that can be modified during exection.
		assert!(!CONTRACT_INFO_CAN_CHANGE);

		// Call stack: BOB -> CHARLIE (trap) -> BOB' (success)
		// This tests verfies some edge case of the contract info cache:
		// We change some value in our contract info before calling into a contract
		// that calls into ourself. This triggers a case where BOBs contract info
		// is written to storage and invalidated by the successful execution of BOB'.
		// The trap of CHARLIE reverts the storage changes to BOB. When the root BOB regains
		// control it reloads its contract info from storage. We check that changes that
		// are made before calling into CHARLIE are not discarded.
		let code_bob = MockLoader::insert(Call, |ctx, _| {
			if ctx.input_data[0] == 0 {
				// DO: modify medata (ContractInfo) of own contract through ctx.ext functions
				assert_eq!(ctx.ext.call(0, CHARLIE, 0, vec![], true), exec_trapped());
				// DO: check that the value is not discarded (query via ctx.ext)
			}
			exec_success()
		});
		let code_charlie = MockLoader::insert(Call, |ctx, _| {
			assert!(ctx.ext.call(0, BOB, 0, vec![99], true).is_ok());
			exec_trapped()
		});

		// This one tests passing the input data into a contract via call.
		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, code_bob);
			place_contract(&CHARLIE, code_charlie);

			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&schedule,
				0,
				vec![0],
				None,
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn recursive_call_during_constructor_fails() {
		let code = MockLoader::insert(Constructor, |ctx, _| {
			assert_matches!(
				ctx.ext.call(0, ctx.ext.address().clone(), 0, vec![], true),
				Err(ExecError{error, ..}) if error == <Error<Test>>::ContractNotFound.into()
			);
			exec_success()
		});

		// This one tests passing the input data into a contract via instantiate.
		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			let subsistence = Contracts::<Test>::subsistence_threshold();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			let executable = MockExecutable::from_storage(code, &schedule, &mut gas_meter).unwrap();

			set_balance(&ALICE, subsistence * 10);

			let result = MockStack::run_instantiate(
				ALICE,
				executable,
				&mut gas_meter,
				&schedule,
				subsistence * 3,
				vec![],
				&[],
				None,
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn printing_works() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			ctx.ext.append_debug_buffer("This is a test");
			ctx.ext.append_debug_buffer("More text");
			exec_success()
		});

		let mut debug_buffer = Vec::new();

		ExtBuilder::default().build().execute_with(|| {
			let subsistence = Contracts::<Test>::subsistence_threshold();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, subsistence * 10);
			place_contract(&BOB, code_hash);
			MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&schedule,
				0,
				vec![],
				Some(&mut debug_buffer),
			)
			.unwrap();
		});

		assert_eq!(&String::from_utf8(debug_buffer).unwrap(), "This is a testMore text");
	}

	#[test]
	fn printing_works_on_fail() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			ctx.ext.append_debug_buffer("This is a test");
			ctx.ext.append_debug_buffer("More text");
			exec_trapped()
		});

		let mut debug_buffer = Vec::new();

		ExtBuilder::default().build().execute_with(|| {
			let subsistence = Contracts::<Test>::subsistence_threshold();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, subsistence * 10);
			place_contract(&BOB, code_hash);
			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&schedule,
				0,
				vec![],
				Some(&mut debug_buffer),
			);
			assert!(result.is_err());
		});

		assert_eq!(&String::from_utf8(debug_buffer).unwrap(), "This is a testMore text");
	}

	#[test]
	fn call_reentry_direct_recursion() {
		// call the contract passed as input with disabled reentry
		let code_bob = MockLoader::insert(Call, |ctx, _| {
			let dest = Decode::decode(&mut ctx.input_data.as_ref()).unwrap();
			ctx.ext.call(0, dest, 0, vec![], false)
		});

		let code_charlie = MockLoader::insert(Call, |_, _| exec_success());

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, code_bob);
			place_contract(&CHARLIE, code_charlie);

			// Calling another contract should succeed
			assert_ok!(MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&schedule,
				0,
				CHARLIE.encode(),
				None,
			));

			// Calling into oneself fails
			assert_err!(
				MockStack::run_call(
					ALICE,
					BOB,
					&mut GasMeter::<Test>::new(GAS_LIMIT),
					&schedule,
					0,
					BOB.encode(),
					None,
				)
				.map_err(|e| e.error),
				<Error<Test>>::ReentranceDenied,
			);
		});
	}

	#[test]
	fn call_deny_reentry() {
		let code_bob = MockLoader::insert(Call, |ctx, _| {
			if ctx.input_data[0] == 0 {
				ctx.ext.call(0, CHARLIE, 0, vec![], false)
			} else {
				exec_success()
			}
		});

		// call BOB with input set to '1'
		let code_charlie =
			MockLoader::insert(Call, |ctx, _| ctx.ext.call(0, BOB, 0, vec![1], true));

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, code_bob);
			place_contract(&CHARLIE, code_charlie);

			// BOB -> CHARLIE -> BOB fails as BOB denies reentry.
			assert_err!(
				MockStack::run_call(
					ALICE,
					BOB,
					&mut GasMeter::<Test>::new(GAS_LIMIT),
					&schedule,
					0,
					vec![0],
					None,
				)
				.map_err(|e| e.error),
				<Error<Test>>::ReentranceDenied,
			);
		});
	}

	#[test]
	fn call_runtime_works() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			let call = Call::System(frame_system::Call::remark_with_event(b"Hello World".to_vec()));
			ctx.ext.call_runtime(call).unwrap();
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let subsistence = Contracts::<Test>::subsistence_threshold();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, subsistence * 10);
			place_contract(&BOB, code_hash);
			System::reset_events();
			MockStack::run_call(ALICE, BOB, &mut gas_meter, &schedule, 0, vec![], None).unwrap();

			let remark_hash = <Test as frame_system::Config>::Hashing::hash(b"Hello World");
			assert_eq!(
				System::events(),
				vec![EventRecord {
					phase: Phase::Initialization,
					event: MetaEvent::System(frame_system::Event::Remarked(BOB, remark_hash)),
					topics: vec![],
				},]
			);
		});
	}

	#[test]
	fn call_runtime_filter() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			use frame_system::Call as SysCall;
			use pallet_balances::Call as BalanceCall;
			use pallet_utility::Call as UtilCall;

			// remark should still be allowed
			let allowed_call = Call::System(SysCall::remark_with_event(b"Hello".to_vec()));

			// transfers are disallowed by the `TestFiler` (see below)
			let forbidden_call = Call::Balances(BalanceCall::transfer(CHARLIE, 22));

			// simple cases: direct call
			assert_err!(ctx.ext.call_runtime(forbidden_call.clone()), BadOrigin);

			// as part of a patch: return is OK (but it interrupted the batch)
			assert_ok!(ctx.ext.call_runtime(Call::Utility(UtilCall::batch(vec![
				allowed_call.clone(),
				forbidden_call,
				allowed_call
			]))),);

			// the transfer wasn't performed
			assert_eq!(get_balance(&CHARLIE), 0);

			exec_success()
		});

		TestFilter::set_filter(|call| match call {
			Call::Balances(pallet_balances::Call::transfer(_, _)) => false,
			_ => true,
		});

		ExtBuilder::default().build().execute_with(|| {
			let subsistence = Contracts::<Test>::subsistence_threshold();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, subsistence * 10);
			place_contract(&BOB, code_hash);
			System::reset_events();
			MockStack::run_call(ALICE, BOB, &mut gas_meter, &schedule, 0, vec![], None).unwrap();

			let remark_hash = <Test as frame_system::Config>::Hashing::hash(b"Hello");
			assert_eq!(
				System::events(),
				vec![
					EventRecord {
						phase: Phase::Initialization,
						event: MetaEvent::System(frame_system::Event::Remarked(BOB, remark_hash)),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: MetaEvent::Utility(pallet_utility::Event::ItemCompleted),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: MetaEvent::Utility(pallet_utility::Event::BatchInterrupted(
							1,
							BadOrigin.into()
						),),
						topics: vec![],
					},
				]
			);
		});
	}
}
