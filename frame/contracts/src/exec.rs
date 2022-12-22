// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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
	gas::GasMeter,
	storage::{self, Storage, WriteOutcome},
	BalanceOf, CodeHash, Config, ContractInfo, ContractInfoOf, DebugBufferVec, Determinism, Error,
	Event, Nonce, Pallet as Contracts, Schedule,
};
use frame_support::{
	crypto::ecdsa::ECDSAExt,
	dispatch::{DispatchError, DispatchResult, DispatchResultWithPostInfo, Dispatchable},
	storage::{with_transaction, TransactionOutcome},
	traits::{Contains, Currency, ExistenceRequirement, OriginTrait, Randomness, Time},
	weights::Weight,
	Blake2_128Concat, BoundedVec, StorageHasher,
};
use frame_system::RawOrigin;
use pallet_contracts_primitives::ExecReturnValue;
use smallvec::{Array, SmallVec};
use sp_core::ecdsa::Public as ECDSAPublic;
use sp_io::{crypto::secp256k1_ecdsa_recover_compressed, hashing::blake2_256};
use sp_runtime::traits::{Convert, Hash};
use sp_std::{marker::PhantomData, mem, prelude::*};

pub type AccountIdOf<T> = <T as frame_system::Config>::AccountId;
pub type MomentOf<T> = <<T as Config>::Time as Time>::Moment;
pub type SeedOf<T> = <T as frame_system::Config>::Hash;
pub type BlockNumberOf<T> = <T as frame_system::Config>::BlockNumber;
pub type ExecResult = Result<ExecReturnValue, ExecError>;

/// A type that represents a topic of an event. At the moment a hash is used.
pub type TopicOf<T> = <T as frame_system::Config>::Hash;

/// Type for fix sized storage key.
pub type FixSizedKey = [u8; 32];

/// Type for variable sized storage key. Used for transparent hashing.
pub type VarSizedKey<T> = BoundedVec<u8, <T as Config>::MaxStorageKeyLen>;

/// Trait for hashing storage keys.
pub trait StorageKey<T>
where
	T: Config,
{
	fn hash(&self) -> Vec<u8>;
}

impl<T: Config> StorageKey<T> for FixSizedKey {
	fn hash(&self) -> Vec<u8> {
		blake2_256(self.as_slice()).to_vec()
	}
}

impl<T> StorageKey<T> for VarSizedKey<T>
where
	T: Config,
{
	fn hash(&self) -> Vec<u8> {
		Blake2_128Concat::hash(self.as_slice())
	}
}

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
	fn call(
		&mut self,
		gas_limit: Weight,
		to: AccountIdOf<Self::T>,
		value: BalanceOf<Self::T>,
		input_data: Vec<u8>,
		allows_reentry: bool,
	) -> Result<ExecReturnValue, ExecError>;

	/// Execute code in the current frame.
	///
	/// Returns the original code size of the called contract.
	fn delegate_call(
		&mut self,
		code: CodeHash<Self::T>,
		input_data: Vec<u8>,
	) -> Result<ExecReturnValue, ExecError>;

	/// Instantiate a contract from the given code.
	///
	/// Returns the original code size of the called contract.
	/// The newly created account will be associated with `code`. `value` specifies the amount of
	/// value transferred from this to the newly created account.
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
	fn get_storage(&mut self, key: &FixSizedKey) -> Option<Vec<u8>>;

	/// This is a variation of `get_storage()` to be used with transparent hashing.
	/// These two will be merged into a single function after some refactoring is done.
	/// Returns the storage entry of the executing account by the given `key`.
	///
	/// Returns `None` if the `key` wasn't previously set by `set_storage` or
	/// was deleted.
	fn get_storage_transparent(&mut self, key: &VarSizedKey<Self::T>) -> Option<Vec<u8>>;

	/// Returns `Some(len)` (in bytes) if a storage item exists at `key`.
	///
	/// Returns `None` if the `key` wasn't previously set by `set_storage` or
	/// was deleted.
	fn get_storage_size(&mut self, key: &FixSizedKey) -> Option<u32>;

	/// This is the variation of `get_storage_size()` to be used with transparent hashing.
	/// These two will be merged into a single function after some refactoring is done.
	/// Returns `Some(len)` (in bytes) if a storage item exists at `key`.
	///
	/// Returns `None` if the `key` wasn't previously set by `set_storage` or
	/// was deleted.
	fn get_storage_size_transparent(&mut self, key: &VarSizedKey<Self::T>) -> Option<u32>;

	/// Sets the storage entry by the given key to the specified value. If `value` is `None` then
	/// the storage entry is deleted.
	fn set_storage(
		&mut self,
		key: &FixSizedKey,
		value: Option<Vec<u8>>,
		take_old: bool,
	) -> Result<WriteOutcome, DispatchError>;

	/// This is the variation of `set_storage()` to be used with transparent hashing.
	/// These two will be merged into a single function after some refactoring is done.
	fn set_storage_transparent(
		&mut self,
		key: &VarSizedKey<Self::T>,
		value: Option<Vec<u8>>,
		take_old: bool,
	) -> Result<WriteOutcome, DispatchError>;

	/// Returns a reference to the account id of the caller.
	fn caller(&self) -> &AccountIdOf<Self::T>;

	/// Check if a contract lives at the specified `address`.
	fn is_contract(&self, address: &AccountIdOf<Self::T>) -> bool;

	/// Returns the code hash of the contract for the given `address`.
	///
	/// Returns `None` if the `address` does not belong to a contract.
	fn code_hash(&self, address: &AccountIdOf<Self::T>) -> Option<CodeHash<Self::T>>;

	/// Returns the code hash of the contract being executed.
	fn own_code_hash(&mut self) -> &CodeHash<Self::T>;

	/// Check if the caller of the current contract is the origin of the whole call stack.
	///
	/// This can be checked with `is_contract(self.caller())` as well.
	/// However, this function does not require any storage lookup and therefore uses less weight.
	fn caller_is_origin(&self) -> bool;

	/// Returns a reference to the account id of the current contract.
	fn address(&self) -> &AccountIdOf<Self::T>;

	/// Returns the balance of the current contract.
	///
	/// The `value_transferred` is already added.
	fn balance(&self) -> BalanceOf<Self::T>;

	/// Returns the value transferred along with this call.
	fn value_transferred(&self) -> BalanceOf<Self::T>;

	/// Returns a reference to the timestamp of the current block
	fn now(&self) -> &MomentOf<Self::T>;

	/// Returns the minimum balance that is required for creating an account.
	fn minimum_balance(&self) -> BalanceOf<Self::T>;

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
	fn append_debug_buffer(&mut self, msg: &str) -> Result<bool, DispatchError>;

	/// Call some dispatchable and return the result.
	fn call_runtime(&self, call: <Self::T as Config>::RuntimeCall) -> DispatchResultWithPostInfo;

	/// Recovers ECDSA compressed public key based on signature and message hash.
	fn ecdsa_recover(&self, signature: &[u8; 65], message_hash: &[u8; 32]) -> Result<[u8; 33], ()>;

	/// Returns Ethereum address from the ECDSA compressed public key.
	fn ecdsa_to_eth_address(&self, pk: &[u8; 33]) -> Result<[u8; 20], ()>;

	/// Tests sometimes need to modify and inspect the contract info directly.
	#[cfg(test)]
	fn contract_info(&mut self) -> &mut ContractInfo<Self::T>;

	/// Sets new code hash for existing contract.
	fn set_code_hash(&mut self, hash: CodeHash<Self::T>) -> Result<(), DispatchError>;

	/// Returns the number of times the currently executing contract exists on the call stack in
	/// addition to the calling instance. A value of 0 means no reentrancy.
	fn reentrance_count(&self) -> u32;

	/// Returns the number of times the specified contract exists on the call stack. Delegated calls
	/// are not calculated as separate entrance.
	/// A value of 0 means it does not exist on the call stack.
	fn account_reentrance_count(&self, account_id: &AccountIdOf<Self::T>) -> u32;

	/// Returns a nonce that is incremented for every instantiated contract.
	fn nonce(&mut self) -> u64;
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

	/// Increment the refcount of a code in-storage by one.
	///
	/// This is needed when the code is not set via instantiate but `seal_set_code_hash`.
	///
	/// # Errors
	///
	/// [`Error::CodeNotFound`] is returned if the specified `code_hash` does not exist.
	fn add_user(code_hash: CodeHash<T>) -> Result<(), DispatchError>;

	/// Decrement the refcount by one if the code exists.
	fn remove_user(code_hash: CodeHash<T>);

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

	/// The code does not contain any instructions which could lead to indeterminism.
	fn is_deterministic(&self) -> bool;
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
	/// The storage meter makes sure that the storage deposit limit is obeyed.
	storage_meter: &'a mut storage::meter::Meter<T>,
	/// The timestamp at the point of call stack instantiation.
	timestamp: MomentOf<T>,
	/// The block number at the time of call stack instantiation.
	block_number: T::BlockNumber,
	/// The nonce is cached here when accessed. It is written back when the call stack
	/// finishes executing. Please refer to [`Nonce`] to a description of
	/// the nonce itself.
	nonce: Option<u64>,
	/// The actual call stack. One entry per nested contract called/instantiated.
	/// This does **not** include the [`Self::first_frame`].
	frames: SmallVec<T::CallStack>,
	/// Statically guarantee that each call stack has at least one frame.
	first_frame: Frame<T>,
	/// A text buffer used to output human readable information.
	///
	/// All the bytes added to this field should be valid UTF-8. The buffer has no defined
	/// structure and is intended to be shown to users as-is for debugging purposes.
	debug_message: Option<&'a mut DebugBufferVec<T>>,
	/// The determinism requirement of this call stack.
	determinism: Determinism,
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
	nested_gas: GasMeter<T>,
	/// The storage meter for the individual call.
	nested_storage: storage::meter::NestedMeter<T>,
	/// If `false` the contract enabled its defense against reentrance attacks.
	allows_reentry: bool,
	/// The caller of the currently executing frame which was spawned by `delegate_call`.
	delegate_caller: Option<T::AccountId>,
}

/// Used in a delegate call frame arguments in order to override the executable and caller.
struct DelegatedCall<T: Config, E> {
	/// The executable which is run instead of the contracts own `executable`.
	executable: E,
	/// The account id of the caller contract.
	caller: T::AccountId,
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
		/// This frame was created by `seal_delegate_call` and hence uses different code than
		/// what is stored at [`Self::dest`]. Its caller ([`Frame::delegated_caller`]) is the
		/// account which called the caller contract
		delegated_call: Option<DelegatedCall<T, E>>,
	},
	Instantiate {
		/// The contract or signed origin which instantiates the new contract.
		sender: T::AccountId,
		/// The nonce that should be used to derive a new trie id for the contract.
		nonce: u64,
		/// The executable whose `deploy` function is run.
		executable: E,
		/// A salt used in the contract address deriviation of the new contract.
		salt: &'a [u8],
		/// The input data is used in the contract address deriviation of the new contract.
		input_data: &'a [u8],
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

impl<T: Config> CachedContract<T> {
	/// Return `Some(ContractInfo)` if the contract is in cached state. `None` otherwise.
	fn into_contract(self) -> Option<ContractInfo<T>> {
		if let CachedContract::Cached(contract) = self {
			Some(contract)
		} else {
			None
		}
	}

	/// Return `Some(&mut ContractInfo)` if the contract is in cached state. `None` otherwise.
	fn as_contract(&mut self) -> Option<&mut ContractInfo<T>> {
		if let CachedContract::Cached(contract) = self {
			Some(contract)
		} else {
			None
		}
	}
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

/// Same as [`Stack::top_frame`].
///
/// We need this access as a macro because sometimes hiding the lifetimes behind
/// a function won't work out.
macro_rules! top_frame {
	($stack:expr) => {
		$stack.frames.last().unwrap_or(&$stack.first_frame)
	};
}

/// Same as [`Stack::top_frame_mut`].
///
/// We need this access as a macro because sometimes hiding the lifetimes behind
/// a function won't work out.
macro_rules! top_frame_mut {
	($stack:expr) => {
		$stack.frames.last_mut().unwrap_or(&mut $stack.first_frame)
	};
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
	E: Executable<T>,
{
	/// Create and run a new call stack by calling into `dest`.
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
		storage_meter: &'a mut storage::meter::Meter<T>,
		schedule: &'a Schedule<T>,
		value: BalanceOf<T>,
		input_data: Vec<u8>,
		debug_message: Option<&'a mut DebugBufferVec<T>>,
		determinism: Determinism,
	) -> Result<ExecReturnValue, ExecError> {
		let (mut stack, executable) = Self::new(
			FrameArgs::Call { dest, cached_info: None, delegated_call: None },
			origin,
			gas_meter,
			storage_meter,
			schedule,
			value,
			debug_message,
			determinism,
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
		storage_meter: &'a mut storage::meter::Meter<T>,
		schedule: &'a Schedule<T>,
		value: BalanceOf<T>,
		input_data: Vec<u8>,
		salt: &[u8],
		debug_message: Option<&'a mut DebugBufferVec<T>>,
	) -> Result<(T::AccountId, ExecReturnValue), ExecError> {
		let (mut stack, executable) = Self::new(
			FrameArgs::Instantiate {
				sender: origin.clone(),
				nonce: <Nonce<T>>::get().wrapping_add(1),
				executable,
				salt,
				input_data: input_data.as_ref(),
			},
			origin,
			gas_meter,
			storage_meter,
			schedule,
			value,
			debug_message,
			Determinism::Deterministic,
		)?;
		let account_id = stack.top_frame().account_id.clone();
		stack.run(executable, input_data).map(|ret| (account_id, ret))
	}

	/// Create a new call stack.
	fn new(
		args: FrameArgs<T, E>,
		origin: T::AccountId,
		gas_meter: &'a mut GasMeter<T>,
		storage_meter: &'a mut storage::meter::Meter<T>,
		schedule: &'a Schedule<T>,
		value: BalanceOf<T>,
		debug_message: Option<&'a mut DebugBufferVec<T>>,
		determinism: Determinism,
	) -> Result<(Self, E), ExecError> {
		let (first_frame, executable, nonce) = Self::new_frame(
			args,
			value,
			gas_meter,
			storage_meter,
			Weight::zero(),
			schedule,
			determinism,
		)?;
		let stack = Self {
			origin,
			schedule,
			gas_meter,
			storage_meter,
			timestamp: T::Time::now(),
			block_number: <frame_system::Pallet<T>>::block_number(),
			nonce,
			first_frame,
			frames: Default::default(),
			debug_message,
			determinism,
			_phantom: Default::default(),
		};

		Ok((stack, executable))
	}

	/// Construct a new frame.
	///
	/// This does not take `self` because when constructing the first frame `self` is
	/// not initialized, yet.
	fn new_frame<S: storage::meter::State>(
		frame_args: FrameArgs<T, E>,
		value_transferred: BalanceOf<T>,
		gas_meter: &mut GasMeter<T>,
		storage_meter: &mut storage::meter::GenericMeter<T, S>,
		gas_limit: Weight,
		schedule: &Schedule<T>,
		determinism: Determinism,
	) -> Result<(Frame<T>, E, Option<u64>), ExecError> {
		let (account_id, contract_info, executable, delegate_caller, entry_point, nonce) =
			match frame_args {
				FrameArgs::Call { dest, cached_info, delegated_call } => {
					let contract = if let Some(contract) = cached_info {
						contract
					} else {
						<ContractInfoOf<T>>::get(&dest).ok_or(<Error<T>>::ContractNotFound)?
					};

					let (executable, delegate_caller) =
						if let Some(DelegatedCall { executable, caller }) = delegated_call {
							(executable, Some(caller))
						} else {
							(E::from_storage(contract.code_hash, schedule, gas_meter)?, None)
						};

					(dest, contract, executable, delegate_caller, ExportedFunction::Call, None)
				},
				FrameArgs::Instantiate { sender, nonce, executable, salt, input_data } => {
					let account_id = Contracts::<T>::contract_address(
						&sender,
						executable.code_hash(),
						input_data,
						salt,
					);
					let trie_id = Storage::<T>::generate_trie_id(&account_id, nonce);
					let contract =
						Storage::<T>::new_contract(&account_id, trie_id, *executable.code_hash())?;
					(
						account_id,
						contract,
						executable,
						None,
						ExportedFunction::Constructor,
						Some(nonce),
					)
				},
			};

		// `AllowIndeterminism` will only be ever set in case of off-chain execution.
		// Instantiations are never allowed even when executing off-chain.
		if !(executable.is_deterministic() ||
			(matches!(determinism, Determinism::AllowIndeterminism) &&
				matches!(entry_point, ExportedFunction::Call)))
		{
			return Err(Error::<T>::Indeterministic.into())
		}

		let frame = Frame {
			delegate_caller,
			value_transferred,
			contract_info: CachedContract::Cached(contract_info),
			account_id,
			entry_point,
			nested_gas: gas_meter.nested(gas_limit)?,
			nested_storage: storage_meter.nested(),
			allows_reentry: true,
		};

		Ok((frame, executable, nonce))
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

		let frame = top_frame_mut!(self);
		let nested_gas = &mut frame.nested_gas;
		let nested_storage = &mut frame.nested_storage;
		let (frame, executable, _) = Self::new_frame(
			frame_args,
			value_transferred,
			nested_gas,
			nested_storage,
			gas_limit,
			self.schedule,
			self.determinism,
		)?;
		self.frames.push(frame);
		Ok(executable)
	}

	/// Run the current (top) frame.
	///
	/// This can be either a call or an instantiate.
	fn run(&mut self, executable: E, input_data: Vec<u8>) -> Result<ExecReturnValue, ExecError> {
		let frame = self.top_frame();
		let entry_point = frame.entry_point;
		let delegated_code_hash =
			if frame.delegate_caller.is_some() { Some(*executable.code_hash()) } else { None };
		let do_transaction = || {
			// We need to charge the storage deposit before the initial transfer so that
			// it can create the account in case the initial transfer is < ed.
			if entry_point == ExportedFunction::Constructor {
				let frame = top_frame_mut!(self);
				frame.nested_storage.charge_instantiate(
					&self.origin,
					&frame.account_id,
					frame.contract_info.get(&frame.account_id),
				)?;
			}

			// Every non delegate call or instantiate also optionally transfers the balance.
			self.initial_transfer()?;

			// Call into the wasm blob.
			let output = executable
				.execute(self, &entry_point, input_data)
				.map_err(|e| ExecError { error: e.error, origin: ErrorOrigin::Callee })?;

			// Avoid useless work that would be reverted anyways.
			if output.did_revert() {
				return Ok(output)
			}

			// Storage limit is enforced as late as possible (when the last frame returns) so that
			// the ordering of storage accesses does not matter.
			if self.frames.is_empty() {
				let frame = &mut self.first_frame;
				frame.contract_info.load(&frame.account_id);
				let contract = frame.contract_info.as_contract();
				frame.nested_storage.enforce_limit(contract)?;
			}

			let frame = self.top_frame();
			let account_id = &frame.account_id;
			match (entry_point, delegated_code_hash) {
				(ExportedFunction::Constructor, _) => {
					// It is not allowed to terminate a contract inside its constructor.
					if matches!(frame.contract_info, CachedContract::Terminated) {
						return Err(Error::<T>::TerminatedInConstructor.into())
					}

					// Deposit an instantiation event.
					Contracts::<T>::deposit_event(
						vec![T::Hashing::hash_of(self.caller()), T::Hashing::hash_of(account_id)],
						Event::Instantiated {
							deployer: self.caller().clone(),
							contract: account_id.clone(),
						},
					);
				},
				(ExportedFunction::Call, Some(code_hash)) => {
					Contracts::<T>::deposit_event(
						vec![T::Hashing::hash_of(account_id), T::Hashing::hash_of(&code_hash)],
						Event::DelegateCalled { contract: account_id.clone(), code_hash },
					);
				},
				(ExportedFunction::Call, None) => {
					let caller = self.caller();
					Contracts::<T>::deposit_event(
						vec![T::Hashing::hash_of(caller), T::Hashing::hash_of(account_id)],
						Event::Called { caller: caller.clone(), contract: account_id.clone() },
					);
				},
			}

			Ok(output)
		};

		// All changes performed by the contract are executed under a storage transaction.
		// This allows for roll back on error. Changes to the cached contract_info are
		// committed or rolled back when popping the frame.
		//
		// `with_transactional` may return an error caused by a limit in the
		// transactional storage depth.
		let transaction_outcome =
			with_transaction(|| -> TransactionOutcome<Result<_, DispatchError>> {
				let output = do_transaction();
				match &output {
					Ok(result) if !result.did_revert() =>
						TransactionOutcome::Commit(Ok((true, output))),
					_ => TransactionOutcome::Rollback(Ok((false, output))),
				}
			});

		let (success, output) = match transaction_outcome {
			// `with_transactional` executed successfully, and we have the expected output.
			Ok((success, output)) => (success, output),
			// `with_transactional` returned an error, and we propagate that error and note no state
			// has changed.
			Err(error) => (false, Err(error.into())),
		};

		self.pop_frame(success);
		output
	}

	/// Remove the current (top) frame from the stack.
	///
	/// This is called after running the current frame. It commits cached values to storage
	/// and invalidates all stale references to it that might exist further down the call stack.
	fn pop_frame(&mut self, persist: bool) {
		// Revert changes to the nonce in case of a failed instantiation.
		if !persist && self.top_frame().entry_point == ExportedFunction::Constructor {
			self.nonce.as_mut().map(|c| *c = c.wrapping_sub(1));
		}

		// Pop the current frame from the stack and return it in case it needs to interact
		// with duplicates that might exist on the stack.
		// A `None` means that we are returning from the `first_frame`.
		let frame = self.frames.pop();

		// Both branches do essentially the same with the exception. The difference is that
		// the else branch does consume the hardcoded `first_frame`.
		if let Some(mut frame) = frame {
			let account_id = &frame.account_id;
			let prev = top_frame_mut!(self);

			prev.nested_gas.absorb_nested(frame.nested_gas);

			// Only gas counter changes are persisted in case of a failure.
			if !persist {
				return
			}

			// Record the storage meter changes of the nested call into the parent meter.
			// If the dropped frame's contract wasn't terminated we update the deposit counter
			// in its contract info. The load is necessary to to pull it from storage in case
			// it was invalidated.
			frame.contract_info.load(account_id);
			let mut contract = frame.contract_info.into_contract();
			prev.nested_storage.absorb(frame.nested_storage, account_id, contract.as_mut());

			// In case the contract wasn't terminated we need to persist changes made to it.
			if let Some(contract) = contract {
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
			self.gas_meter.absorb_nested(mem::take(&mut self.first_frame.nested_gas));
			if !persist {
				return
			}
			let mut contract = self.first_frame.contract_info.as_contract();
			self.storage_meter.absorb(
				mem::take(&mut self.first_frame.nested_storage),
				&self.first_frame.account_id,
				contract.as_deref_mut(),
			);
			if let Some(contract) = contract {
				<ContractInfoOf<T>>::insert(&self.first_frame.account_id, contract);
			}
			if let Some(nonce) = self.nonce {
				<Nonce<T>>::set(nonce);
			}
		}
	}

	/// Transfer some funds from `from` to `to`.
	fn transfer(
		existence_requirement: ExistenceRequirement,
		from: &T::AccountId,
		to: &T::AccountId,
		value: BalanceOf<T>,
	) -> DispatchResult {
		T::Currency::transfer(from, to, value, existence_requirement)
			.map_err(|_| Error::<T>::TransferFailed)?;
		Ok(())
	}

	// The transfer as performed by a call or instantiate.
	fn initial_transfer(&self) -> DispatchResult {
		let frame = self.top_frame();

		// If it is a delegate call, then we've already transferred tokens in the
		// last non-delegate frame.
		if frame.delegate_caller.is_some() {
			return Ok(())
		}

		let value = frame.value_transferred;
		Self::transfer(ExistenceRequirement::KeepAlive, self.caller(), &frame.account_id, value)
	}

	/// Reference to the current (top) frame.
	fn top_frame(&self) -> &Frame<T> {
		top_frame!(self)
	}

	/// Mutable reference to the current (top) frame.
	fn top_frame_mut(&mut self) -> &mut Frame<T> {
		top_frame_mut!(self)
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

	/// Increments and returns the next nonce. Pulls it from storage if it isn't in cache.
	fn next_nonce(&mut self) -> u64 {
		let next = self.nonce().wrapping_add(1);
		self.nonce = Some(next);
		next
	}
}

impl<'a, T, E> Ext for Stack<'a, T, E>
where
	T: Config,
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
			let executable = self.push_frame(
				FrameArgs::Call { dest: to, cached_info, delegated_call: None },
				value,
				gas_limit,
			)?;
			self.run(executable, input_data)
		};

		// We need to make sure to reset `allows_reentry` even on failure.
		let result = try_call();

		// Protection is on a per call basis.
		self.top_frame_mut().allows_reentry = true;

		result
	}

	fn delegate_call(
		&mut self,
		code_hash: CodeHash<Self::T>,
		input_data: Vec<u8>,
	) -> Result<ExecReturnValue, ExecError> {
		let executable = E::from_storage(code_hash, self.schedule, self.gas_meter())?;
		let top_frame = self.top_frame_mut();
		let contract_info = top_frame.contract_info().clone();
		let account_id = top_frame.account_id.clone();
		let value = top_frame.value_transferred;
		let executable = self.push_frame(
			FrameArgs::Call {
				dest: account_id,
				cached_info: Some(contract_info),
				delegated_call: Some(DelegatedCall { executable, caller: self.caller().clone() }),
			},
			value,
			Weight::zero(),
		)?;
		self.run(executable, input_data)
	}

	fn instantiate(
		&mut self,
		gas_limit: Weight,
		code_hash: CodeHash<T>,
		value: BalanceOf<T>,
		input_data: Vec<u8>,
		salt: &[u8],
	) -> Result<(AccountIdOf<T>, ExecReturnValue), ExecError> {
		let executable = E::from_storage(code_hash, self.schedule, self.gas_meter())?;
		let nonce = self.next_nonce();
		let executable = self.push_frame(
			FrameArgs::Instantiate {
				sender: self.top_frame().account_id.clone(),
				nonce,
				executable,
				salt,
				input_data: input_data.as_ref(),
			},
			value,
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
		frame.nested_storage.terminate(&info);
		Storage::<T>::queue_trie_for_deletion(&info)?;
		<Stack<'a, T, E>>::transfer(
			ExistenceRequirement::AllowDeath,
			&frame.account_id,
			beneficiary,
			T::Currency::free_balance(&frame.account_id),
		)?;
		ContractInfoOf::<T>::remove(&frame.account_id);
		E::remove_user(info.code_hash);
		Contracts::<T>::deposit_event(
			vec![T::Hashing::hash_of(&frame.account_id), T::Hashing::hash_of(&beneficiary)],
			Event::Terminated {
				contract: frame.account_id.clone(),
				beneficiary: beneficiary.clone(),
			},
		);
		Ok(())
	}

	fn transfer(&mut self, to: &T::AccountId, value: BalanceOf<T>) -> DispatchResult {
		Self::transfer(ExistenceRequirement::KeepAlive, &self.top_frame().account_id, to, value)
	}

	fn get_storage(&mut self, key: &FixSizedKey) -> Option<Vec<u8>> {
		Storage::<T>::read(&self.top_frame_mut().contract_info().trie_id, key)
	}

	fn get_storage_transparent(&mut self, key: &VarSizedKey<T>) -> Option<Vec<u8>> {
		Storage::<T>::read(&self.top_frame_mut().contract_info().trie_id, key)
	}

	fn get_storage_size(&mut self, key: &FixSizedKey) -> Option<u32> {
		Storage::<T>::size(&self.top_frame_mut().contract_info().trie_id, key)
	}

	fn get_storage_size_transparent(&mut self, key: &VarSizedKey<T>) -> Option<u32> {
		Storage::<T>::size(&self.top_frame_mut().contract_info().trie_id, key)
	}

	fn set_storage(
		&mut self,
		key: &FixSizedKey,
		value: Option<Vec<u8>>,
		take_old: bool,
	) -> Result<WriteOutcome, DispatchError> {
		let frame = self.top_frame_mut();
		Storage::<T>::write(
			&frame.contract_info.get(&frame.account_id).trie_id,
			key,
			value,
			Some(&mut frame.nested_storage),
			take_old,
		)
	}

	fn set_storage_transparent(
		&mut self,
		key: &VarSizedKey<T>,
		value: Option<Vec<u8>>,
		take_old: bool,
	) -> Result<WriteOutcome, DispatchError> {
		let frame = self.top_frame_mut();
		Storage::<T>::write(
			&frame.contract_info.get(&frame.account_id).trie_id,
			key,
			value,
			Some(&mut frame.nested_storage),
			take_old,
		)
	}

	fn address(&self) -> &T::AccountId {
		&self.top_frame().account_id
	}

	fn caller(&self) -> &T::AccountId {
		if let Some(caller) = &self.top_frame().delegate_caller {
			caller
		} else {
			self.frames().nth(1).map(|f| &f.account_id).unwrap_or(&self.origin)
		}
	}

	fn is_contract(&self, address: &T::AccountId) -> bool {
		ContractInfoOf::<T>::contains_key(&address)
	}

	fn code_hash(&self, address: &T::AccountId) -> Option<CodeHash<Self::T>> {
		<ContractInfoOf<T>>::get(&address).map(|contract| contract.code_hash)
	}

	fn own_code_hash(&mut self) -> &CodeHash<Self::T> {
		&self.top_frame_mut().contract_info().code_hash
	}

	fn caller_is_origin(&self) -> bool {
		self.caller() == &self.origin
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

	fn deposit_event(&mut self, topics: Vec<T::Hash>, data: Vec<u8>) {
		Contracts::<Self::T>::deposit_event(
			topics,
			Event::ContractEmitted { contract: self.top_frame().account_id.clone(), data },
		);
	}

	fn block_number(&self) -> T::BlockNumber {
		self.block_number
	}

	fn max_value_size(&self) -> u32 {
		self.schedule.limits.payload_len
	}

	fn get_weight_price(&self, weight: Weight) -> BalanceOf<Self::T> {
		T::WeightPrice::convert(weight)
	}

	fn schedule(&self) -> &Schedule<Self::T> {
		self.schedule
	}

	fn gas_meter(&mut self) -> &mut GasMeter<Self::T> {
		&mut self.top_frame_mut().nested_gas
	}

	fn append_debug_buffer(&mut self, msg: &str) -> Result<bool, DispatchError> {
		if let Some(buffer) = &mut self.debug_message {
			if !msg.is_empty() {
				buffer
					.try_extend(&mut msg.bytes())
					.map_err(|_| Error::<T>::DebugBufferExhausted)?;
			}
			Ok(true)
		} else {
			Ok(false)
		}
	}

	fn call_runtime(&self, call: <Self::T as Config>::RuntimeCall) -> DispatchResultWithPostInfo {
		let mut origin: T::RuntimeOrigin = RawOrigin::Signed(self.address().clone()).into();
		origin.add_filter(T::CallFilter::contains);
		call.dispatch(origin)
	}

	fn ecdsa_recover(&self, signature: &[u8; 65], message_hash: &[u8; 32]) -> Result<[u8; 33], ()> {
		secp256k1_ecdsa_recover_compressed(signature, message_hash).map_err(|_| ())
	}

	fn ecdsa_to_eth_address(&self, pk: &[u8; 33]) -> Result<[u8; 20], ()> {
		ECDSAPublic(*pk).to_eth_address()
	}

	#[cfg(test)]
	fn contract_info(&mut self) -> &mut ContractInfo<Self::T> {
		self.top_frame_mut().contract_info()
	}

	fn set_code_hash(&mut self, hash: CodeHash<Self::T>) -> Result<(), DispatchError> {
		let frame = top_frame_mut!(self);
		if !E::from_storage(hash, self.schedule, &mut frame.nested_gas)?.is_deterministic() {
			return Err(<Error<T>>::Indeterministic.into())
		}
		E::add_user(hash)?;
		let prev_hash = frame.contract_info().code_hash;
		E::remove_user(prev_hash);
		frame.contract_info().code_hash = hash;
		Contracts::<Self::T>::deposit_event(
			vec![T::Hashing::hash_of(&frame.account_id), hash, prev_hash],
			Event::ContractCodeUpdated {
				contract: frame.account_id.clone(),
				new_code_hash: hash,
				old_code_hash: prev_hash,
			},
		);
		Ok(())
	}

	fn reentrance_count(&self) -> u32 {
		let id: &AccountIdOf<Self::T> = &self.top_frame().account_id;
		self.account_reentrance_count(id).saturating_sub(1)
	}

	fn account_reentrance_count(&self, account_id: &AccountIdOf<Self::T>) -> u32 {
		self.frames()
			.filter(|f| f.delegate_caller.is_none() && &f.account_id == account_id)
			.count() as u32
	}

	fn nonce(&mut self) -> u64 {
		if let Some(current) = self.nonce {
			current
		} else {
			let current = <Nonce<T>>::get();
			self.nonce = Some(current);
			current
		}
	}
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
			test_utils::{get_balance, hash, place_contract, set_balance},
			ExtBuilder, RuntimeCall, RuntimeEvent as MetaEvent, Test, TestFilter, ALICE, BOB,
			CHARLIE, GAS_LIMIT,
		},
		Error,
	};
	use assert_matches::assert_matches;
	use codec::{Decode, Encode};
	use frame_support::{assert_err, assert_ok, parameter_types};
	use frame_system::{EventRecord, Phase};
	use pallet_contracts_primitives::ReturnFlags;
	use pretty_assertions::assert_eq;
	use sp_runtime::{traits::Hash, DispatchError};
	use std::{
		cell::RefCell,
		collections::hash_map::{Entry, HashMap},
		rc::Rc,
	};

	type System = frame_system::Pallet<Test>;

	type MockStack<'a> = Stack<'a, Test, MockExecutable>;

	parameter_types! {
		static Loader: MockLoader = MockLoader::default();
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

	#[derive(Default, Clone)]
	pub struct MockLoader {
		map: HashMap<CodeHash<Test>, MockExecutable>,
		counter: u64,
	}

	impl MockLoader {
		fn insert(
			func_type: ExportedFunction,
			f: impl Fn(MockCtx, &MockExecutable) -> ExecResult + 'static,
		) -> CodeHash<Test> {
			Loader::mutate(|loader| {
				// Generate code hashes as monotonically increasing values.
				let hash = <Test as frame_system::Config>::Hash::from_low_u64_be(loader.counter);
				loader.counter += 1;
				loader.map.insert(
					hash,
					MockExecutable { func: Rc::new(f), func_type, code_hash: hash, refcount: 1 },
				);
				hash
			})
		}

		fn increment_refcount(code_hash: CodeHash<Test>) -> Result<(), DispatchError> {
			Loader::mutate(|loader| {
				match loader.map.entry(code_hash) {
					Entry::Vacant(_) => Err(<Error<Test>>::CodeNotFound)?,
					Entry::Occupied(mut entry) => entry.get_mut().refcount += 1,
				}
				Ok(())
			})
		}

		fn decrement_refcount(code_hash: CodeHash<Test>) {
			use std::collections::hash_map::Entry::Occupied;
			Loader::mutate(|loader| {
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
			Loader::mutate(|loader| {
				loader.map.get(&code_hash).cloned().ok_or(Error::<Test>::CodeNotFound.into())
			})
		}

		fn add_user(code_hash: CodeHash<Test>) -> Result<(), DispatchError> {
			MockLoader::increment_refcount(code_hash)
		}

		fn remove_user(code_hash: CodeHash<Test>) {
			MockLoader::decrement_refcount(code_hash);
		}

		fn execute<E: Ext<T = Test>>(
			self,
			ext: &mut E,
			function: &ExportedFunction,
			input_data: Vec<u8>,
		) -> ExecResult {
			if let &Constructor = function {
				Self::add_user(self.code_hash).unwrap();
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

		fn is_deterministic(&self) -> bool {
			true
		}
	}

	fn exec_success() -> ExecResult {
		Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Vec::new() })
	}

	fn exec_trapped() -> ExecResult {
		Err(ExecError { error: <Error<Test>>::ContractTrapped.into(), origin: ErrorOrigin::Callee })
	}

	#[test]
	fn it_works() {
		parameter_types! {
			static TestData: Vec<usize> = vec![0];
		}

		let value = Default::default();
		let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
		let exec_ch = MockLoader::insert(Call, |_ctx, _executable| {
			TestData::mutate(|data| data.push(1));
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, exec_ch);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), value).unwrap();

			assert_matches!(
				MockStack::run_call(
					ALICE,
					BOB,
					&mut gas_meter,
					&mut storage_meter,
					&schedule,
					value,
					vec![],
					None,
					Determinism::Deterministic,
				),
				Ok(_)
			);
		});

		assert_eq!(TestData::get(), vec![0, 1]);
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

			MockStack::transfer(ExistenceRequirement::KeepAlive, &origin, &dest, 55).unwrap();

			assert_eq!(get_balance(&origin), 45);
			assert_eq!(get_balance(&dest), 55);
		});
	}

	#[test]
	fn correct_transfer_on_call() {
		let origin = ALICE;
		let dest = BOB;
		let value = 55;

		let success_ch = MockLoader::insert(Call, move |ctx, _| {
			assert_eq!(ctx.ext.value_transferred(), value);
			Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Vec::new() })
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&dest, success_ch);
			set_balance(&origin, 100);
			let balance = get_balance(&dest);
			let mut storage_meter = storage::meter::Meter::new(&origin, Some(0), 55).unwrap();

			let _ = MockStack::run_call(
				origin.clone(),
				dest.clone(),
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				value,
				vec![],
				None,
				Determinism::Deterministic,
			)
			.unwrap();

			assert_eq!(get_balance(&origin), 100 - value);
			assert_eq!(get_balance(&dest), balance + value);
		});
	}

	#[test]
	fn correct_transfer_on_delegate_call() {
		let origin = ALICE;
		let dest = BOB;
		let value = 35;

		let success_ch = MockLoader::insert(Call, move |ctx, _| {
			assert_eq!(ctx.ext.value_transferred(), value);
			Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Vec::new() })
		});

		let delegate_ch = MockLoader::insert(Call, move |ctx, _| {
			assert_eq!(ctx.ext.value_transferred(), value);
			let _ = ctx.ext.delegate_call(success_ch, Vec::new())?;
			Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Vec::new() })
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&dest, delegate_ch);
			set_balance(&origin, 100);
			let balance = get_balance(&dest);
			let mut storage_meter = storage::meter::Meter::new(&origin, Some(0), 55).unwrap();

			let _ = MockStack::run_call(
				origin.clone(),
				dest.clone(),
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				value,
				vec![],
				None,
				Determinism::Deterministic,
			)
			.unwrap();

			assert_eq!(get_balance(&origin), 100 - value);
			assert_eq!(get_balance(&dest), balance + value);
		});
	}

	#[test]
	fn changes_are_reverted_on_failing_call() {
		// This test verifies that changes are reverted on a call which fails (or equally, returns
		// a non-zero status code).
		let origin = ALICE;
		let dest = BOB;

		let return_ch = MockLoader::insert(Call, |_, _| {
			Ok(ExecReturnValue { flags: ReturnFlags::REVERT, data: Vec::new() })
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&dest, return_ch);
			set_balance(&origin, 100);
			let balance = get_balance(&dest);
			let mut storage_meter = storage::meter::Meter::new(&origin, Some(0), 55).unwrap();

			let output = MockStack::run_call(
				origin.clone(),
				dest.clone(),
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				55,
				vec![],
				None,
				Determinism::Deterministic,
			)
			.unwrap();

			assert!(output.did_revert());
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

			let result = MockStack::transfer(ExistenceRequirement::KeepAlive, &origin, &dest, 100);

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
			Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: vec![1, 2, 3, 4] })
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			let mut storage_meter = storage::meter::Meter::new(&origin, Some(0), 0).unwrap();
			place_contract(&BOB, return_ch);

			let result = MockStack::run_call(
				origin,
				dest,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic,
			);

			let output = result.unwrap();
			assert!(!output.did_revert());
			assert_eq!(output.data, vec![1, 2, 3, 4]);
		});
	}

	#[test]
	fn output_is_returned_on_failure() {
		// Verifies that if a contract returns data with a failing exit status, this data
		// is returned from the execution context.
		let origin = ALICE;
		let dest = BOB;
		let return_ch = MockLoader::insert(Call, |_, _| {
			Ok(ExecReturnValue { flags: ReturnFlags::REVERT, data: vec![1, 2, 3, 4] })
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, return_ch);
			let mut storage_meter = storage::meter::Meter::new(&origin, Some(0), 0).unwrap();

			let result = MockStack::run_call(
				origin,
				dest,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic,
			);

			let output = result.unwrap();
			assert!(output.did_revert());
			assert_eq!(output.data, vec![1, 2, 3, 4]);
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
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();

			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				vec![1, 2, 3, 4],
				None,
				Determinism::Deterministic,
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
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			let executable =
				MockExecutable::from_storage(input_data_ch, &schedule, &mut gas_meter).unwrap();
			set_balance(&ALICE, min_balance * 1000);
			let mut storage_meter =
				storage::meter::Meter::new(&ALICE, Some(min_balance * 100), min_balance).unwrap();

			let result = MockStack::run_instantiate(
				ALICE,
				executable,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				min_balance,
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
		parameter_types! {
			static ReachedBottom: bool = false;
		}
		let value = Default::default();
		let recurse_ch = MockLoader::insert(Call, |ctx, _| {
			// Try to call into yourself.
			let r = ctx.ext.call(Weight::zero(), BOB, 0, vec![], true);

			ReachedBottom::mutate(|reached_bottom| {
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
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), value).unwrap();

			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				value,
				vec![],
				None,
				Determinism::Deterministic,
			);

			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn caller_returns_proper_values() {
		let origin = ALICE;
		let dest = BOB;

		parameter_types! {
			static WitnessedCallerBob: Option<AccountIdOf<Test>> = None;
			static WitnessedCallerCharlie: Option<AccountIdOf<Test>> = None;
		}

		let bob_ch = MockLoader::insert(Call, |ctx, _| {
			// Record the caller for bob.
			WitnessedCallerBob::mutate(|caller| *caller = Some(ctx.ext.caller().clone()));

			// Call into CHARLIE contract.
			assert_matches!(ctx.ext.call(Weight::zero(), CHARLIE, 0, vec![], true), Ok(_));
			exec_success()
		});
		let charlie_ch = MockLoader::insert(Call, |ctx, _| {
			// Record the caller for charlie.
			WitnessedCallerCharlie::mutate(|caller| *caller = Some(ctx.ext.caller().clone()));
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&dest, bob_ch);
			place_contract(&CHARLIE, charlie_ch);
			let mut storage_meter = storage::meter::Meter::new(&origin, Some(0), 0).unwrap();

			let result = MockStack::run_call(
				origin.clone(),
				dest.clone(),
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic,
			);

			assert_matches!(result, Ok(_));
		});

		assert_eq!(WitnessedCallerBob::get(), Some(origin));
		assert_eq!(WitnessedCallerCharlie::get(), Some(dest));
	}

	#[test]
	fn is_contract_returns_proper_values() {
		let bob_ch = MockLoader::insert(Call, |ctx, _| {
			// Verify that BOB is a contract
			assert!(ctx.ext.is_contract(&BOB));
			// Verify that ALICE is not a contract
			assert!(!ctx.ext.is_contract(&ALICE));
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, bob_ch);

			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();
			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic,
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn code_hash_returns_proper_values() {
		let code_bob = MockLoader::insert(Call, |ctx, _| {
			// ALICE is not a contract and hence she does not have a code_hash
			assert!(ctx.ext.code_hash(&ALICE).is_none());
			// BOB is a contract and hence he has a code_hash
			assert!(ctx.ext.code_hash(&BOB).is_some());
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, code_bob);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();
			// ALICE (not contract) -> BOB (contract)
			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				vec![0],
				None,
				Determinism::Deterministic,
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn own_code_hash_returns_proper_values() {
		let bob_ch = MockLoader::insert(Call, |ctx, _| {
			let code_hash = ctx.ext.code_hash(&BOB).unwrap();
			assert_eq!(*ctx.ext.own_code_hash(), code_hash);
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, bob_ch);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();
			// ALICE (not contract) -> BOB (contract)
			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				vec![0],
				None,
				Determinism::Deterministic,
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn caller_is_origin_returns_proper_values() {
		let code_charlie = MockLoader::insert(Call, |ctx, _| {
			// BOB is not the origin of the stack call
			assert!(!ctx.ext.caller_is_origin());
			exec_success()
		});

		let code_bob = MockLoader::insert(Call, |ctx, _| {
			// ALICE is the origin of the call stack
			assert!(ctx.ext.caller_is_origin());
			// BOB calls CHARLIE
			ctx.ext.call(Weight::zero(), CHARLIE, 0, vec![], true)
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, code_bob);
			place_contract(&CHARLIE, code_charlie);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();
			// ALICE -> BOB (caller is origin) -> CHARLIE (caller is not origin)
			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				vec![0],
				None,
				Determinism::Deterministic,
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn address_returns_proper_values() {
		let bob_ch = MockLoader::insert(Call, |ctx, _| {
			// Verify that address matches BOB.
			assert_eq!(*ctx.ext.address(), BOB);

			// Call into charlie contract.
			assert_matches!(ctx.ext.call(Weight::zero(), CHARLIE, 0, vec![], true), Ok(_));
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
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();

			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic,
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
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();

			assert_matches!(
				MockStack::run_instantiate(
					ALICE,
					executable,
					&mut gas_meter,
					&mut storage_meter,
					&schedule,
					0, // <- zero value
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
			Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: vec![80, 65, 83, 83] })
		});

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			let executable =
				MockExecutable::from_storage(dummy_ch, &schedule, &mut gas_meter).unwrap();
			set_balance(&ALICE, min_balance * 1000);
			let mut storage_meter =
				storage::meter::Meter::new(&ALICE, Some(min_balance * 100), min_balance).unwrap();

			let instantiated_contract_address = assert_matches!(
				MockStack::run_instantiate(
					ALICE,
					executable,
					&mut gas_meter,
					&mut storage_meter,
					&schedule,
					min_balance,
					vec![],
					&[],
					None,
				),
				Ok((address, ref output)) if output.data == vec![80, 65, 83, 83] => address
			);

			// Check that the newly created account has the expected code hash and
			// there are instantiation event.
			assert_eq!(
				Storage::<Test>::code_hash(&instantiated_contract_address).unwrap(),
				dummy_ch
			);
			assert_eq!(
				&events(),
				&[Event::Instantiated { deployer: ALICE, contract: instantiated_contract_address }]
			);
		});
	}

	#[test]
	fn instantiation_fails_with_failing_output() {
		let dummy_ch = MockLoader::insert(Constructor, |_, _| {
			Ok(ExecReturnValue { flags: ReturnFlags::REVERT, data: vec![70, 65, 73, 76] })
		});

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			let executable =
				MockExecutable::from_storage(dummy_ch, &schedule, &mut gas_meter).unwrap();
			set_balance(&ALICE, min_balance * 1000);
			let mut storage_meter =
				storage::meter::Meter::new(&ALICE, Some(min_balance * 100), min_balance).unwrap();

			let instantiated_contract_address = assert_matches!(
				MockStack::run_instantiate(
					ALICE,
					executable,
					&mut gas_meter,
					&mut storage_meter,
					&schedule,
					min_balance,
					vec![],
					&[],
					None,
				),
				Ok((address, ref output)) if output.data == vec![70, 65, 73, 76] => address
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
			let instantiated_contract_address = Rc::clone(&instantiated_contract_address);
			move |ctx, _| {
				// Instantiate a contract and save it's address in `instantiated_contract_address`.
				let (address, output) = ctx
					.ext
					.instantiate(
						Weight::zero(),
						dummy_ch,
						<Test as Config>::Currency::minimum_balance(),
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
			let min_balance = <Test as Config>::Currency::minimum_balance();
			set_balance(&ALICE, min_balance * 100);
			place_contract(&BOB, instantiator_ch);
			let mut storage_meter =
				storage::meter::Meter::new(&ALICE, Some(min_balance * 10), min_balance * 10)
					.unwrap();

			assert_matches!(
				MockStack::run_call(
					ALICE,
					BOB,
					&mut GasMeter::<Test>::new(GAS_LIMIT),
					&mut storage_meter,
					&schedule,
					min_balance * 10,
					vec![],
					None,
					Determinism::Deterministic,
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
			assert_eq!(
				&events(),
				&[
					Event::Instantiated { deployer: BOB, contract: instantiated_contract_address },
					Event::Called { caller: ALICE, contract: BOB },
				]
			);
		});
	}

	#[test]
	fn instantiation_traps() {
		let dummy_ch = MockLoader::insert(Constructor, |_, _| Err("It's a trap!".into()));
		let instantiator_ch = MockLoader::insert(Call, {
			move |ctx, _| {
				// Instantiate a contract and save it's address in `instantiated_contract_address`.
				assert_matches!(
					ctx.ext.instantiate(
						Weight::zero(),
						dummy_ch,
						<Test as Config>::Currency::minimum_balance(),
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
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(100), 0).unwrap();

			assert_matches!(
				MockStack::run_call(
					ALICE,
					BOB,
					&mut GasMeter::<Test>::new(GAS_LIMIT),
					&mut storage_meter,
					&schedule,
					0,
					vec![],
					None,
					Determinism::Deterministic,
				),
				Ok(_)
			);

			// The contract wasn't instantiated so we don't expect to see an instantiation
			// event here.
			assert_eq!(&events(), &[Event::Called { caller: ALICE, contract: BOB },]);
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
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(100), 100).unwrap();

			assert_eq!(
				MockStack::run_instantiate(
					ALICE,
					executable,
					&mut gas_meter,
					&mut storage_meter,
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
				let info = ctx.ext.contract_info();
				assert_eq!(info.storage_byte_deposit, 0);
				info.storage_byte_deposit = 42;
				assert_eq!(ctx.ext.call(Weight::zero(), CHARLIE, 0, vec![], true), exec_trapped());
				assert_eq!(ctx.ext.contract_info().storage_byte_deposit, 42);
			}
			exec_success()
		});
		let code_charlie = MockLoader::insert(Call, |ctx, _| {
			assert!(ctx.ext.call(Weight::zero(), BOB, 0, vec![99], true).is_ok());
			exec_trapped()
		});

		// This one tests passing the input data into a contract via call.
		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, code_bob);
			place_contract(&CHARLIE, code_charlie);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();

			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				vec![0],
				None,
				Determinism::Deterministic,
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn recursive_call_during_constructor_fails() {
		let code = MockLoader::insert(Constructor, |ctx, _| {
			assert_matches!(
				ctx.ext.call(Weight::zero(), ctx.ext.address().clone(), 0, vec![], true),
				Err(ExecError{error, ..}) if error == <Error<Test>>::ContractNotFound.into()
			);
			exec_success()
		});

		// This one tests passing the input data into a contract via instantiate.
		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			let executable = MockExecutable::from_storage(code, &schedule, &mut gas_meter).unwrap();
			set_balance(&ALICE, min_balance * 1000);
			let mut storage_meter =
				storage::meter::Meter::new(&ALICE, Some(min_balance * 100), min_balance).unwrap();

			let result = MockStack::run_instantiate(
				ALICE,
				executable,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				min_balance,
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
			ctx.ext
				.append_debug_buffer("This is a test")
				.expect("Maximum allowed debug buffer size exhausted!");
			ctx.ext
				.append_debug_buffer("More text")
				.expect("Maximum allowed debug buffer size exhausted!");
			exec_success()
		});

		let mut debug_buffer = DebugBufferVec::<Test>::try_from(Vec::new()).unwrap();

		ExtBuilder::default().build().execute_with(|| {
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 10);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();
			MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				Some(&mut debug_buffer),
				Determinism::Deterministic,
			)
			.unwrap();
		});

		assert_eq!(&String::from_utf8(debug_buffer.to_vec()).unwrap(), "This is a testMore text");
	}

	#[test]
	fn printing_works_on_fail() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			ctx.ext
				.append_debug_buffer("This is a test")
				.expect("Maximum allowed debug buffer size exhausted!");
			ctx.ext
				.append_debug_buffer("More text")
				.expect("Maximum allowed debug buffer size exhausted!");
			exec_trapped()
		});

		let mut debug_buffer = DebugBufferVec::<Test>::try_from(Vec::new()).unwrap();

		ExtBuilder::default().build().execute_with(|| {
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 10);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();
			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				Some(&mut debug_buffer),
				Determinism::Deterministic,
			);
			assert!(result.is_err());
		});

		assert_eq!(&String::from_utf8(debug_buffer.to_vec()).unwrap(), "This is a testMore text");
	}

	#[test]
	fn debug_buffer_is_limited() {
		let code_hash = MockLoader::insert(Call, move |ctx, _| {
			ctx.ext.append_debug_buffer("overflowing bytes")?;
			exec_success()
		});

		// Pre-fill the buffer up to its limit
		let mut debug_buffer =
			DebugBufferVec::<Test>::try_from(vec![0u8; DebugBufferVec::<Test>::bound()]).unwrap();

		ExtBuilder::default().build().execute_with(|| {
			let schedule: Schedule<Test> = <Test as Config>::Schedule::get();
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 10);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();
			assert_err!(
				MockStack::run_call(
					ALICE,
					BOB,
					&mut gas_meter,
					&mut storage_meter,
					&schedule,
					0,
					vec![],
					Some(&mut debug_buffer),
					Determinism::Deterministic,
				)
				.map_err(|e| e.error),
				Error::<Test>::DebugBufferExhausted
			);
		});
	}

	#[test]
	fn call_reentry_direct_recursion() {
		// call the contract passed as input with disabled reentry
		let code_bob = MockLoader::insert(Call, |ctx, _| {
			let dest = Decode::decode(&mut ctx.input_data.as_ref()).unwrap();
			ctx.ext.call(Weight::zero(), dest, 0, vec![], false)
		});

		let code_charlie = MockLoader::insert(Call, |_, _| exec_success());

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, code_bob);
			place_contract(&CHARLIE, code_charlie);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();

			// Calling another contract should succeed
			assert_ok!(MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				CHARLIE.encode(),
				None,
				Determinism::Deterministic
			));

			// Calling into oneself fails
			assert_err!(
				MockStack::run_call(
					ALICE,
					BOB,
					&mut GasMeter::<Test>::new(GAS_LIMIT),
					&mut storage_meter,
					&schedule,
					0,
					BOB.encode(),
					None,
					Determinism::Deterministic
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
				ctx.ext.call(Weight::zero(), CHARLIE, 0, vec![], false)
			} else {
				exec_success()
			}
		});

		// call BOB with input set to '1'
		let code_charlie =
			MockLoader::insert(Call, |ctx, _| ctx.ext.call(Weight::zero(), BOB, 0, vec![1], true));

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, code_bob);
			place_contract(&CHARLIE, code_charlie);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();

			// BOB -> CHARLIE -> BOB fails as BOB denies reentry.
			assert_err!(
				MockStack::run_call(
					ALICE,
					BOB,
					&mut GasMeter::<Test>::new(GAS_LIMIT),
					&mut storage_meter,
					&schedule,
					0,
					vec![0],
					None,
					Determinism::Deterministic
				)
				.map_err(|e| e.error),
				<Error<Test>>::ReentranceDenied,
			);
		});
	}

	#[test]
	fn call_runtime_works() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			let call = RuntimeCall::System(frame_system::Call::remark_with_event {
				remark: b"Hello World".to_vec(),
			});
			ctx.ext.call_runtime(call).unwrap();
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 10);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();
			System::reset_events();
			MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic,
			)
			.unwrap();

			let remark_hash = <Test as frame_system::Config>::Hashing::hash(b"Hello World");
			assert_eq!(
				System::events(),
				vec![
					EventRecord {
						phase: Phase::Initialization,
						event: MetaEvent::System(frame_system::Event::Remarked {
							sender: BOB,
							hash: remark_hash
						}),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: MetaEvent::Contracts(crate::Event::Called {
							caller: ALICE,
							contract: BOB,
						}),
						topics: vec![hash(&ALICE), hash(&BOB)],
					},
				]
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
			let allowed_call =
				RuntimeCall::System(SysCall::remark_with_event { remark: b"Hello".to_vec() });

			// transfers are disallowed by the `TestFiler` (see below)
			let forbidden_call =
				RuntimeCall::Balances(BalanceCall::transfer { dest: CHARLIE, value: 22 });

			// simple cases: direct call
			assert_err!(
				ctx.ext.call_runtime(forbidden_call.clone()),
				frame_system::Error::<Test>::CallFiltered
			);

			// as part of a patch: return is OK (but it interrupted the batch)
			assert_ok!(ctx.ext.call_runtime(RuntimeCall::Utility(UtilCall::batch {
				calls: vec![allowed_call.clone(), forbidden_call, allowed_call]
			})),);

			// the transfer wasn't performed
			assert_eq!(get_balance(&CHARLIE), 0);

			exec_success()
		});

		TestFilter::set_filter(|call| match call {
			RuntimeCall::Balances(pallet_balances::Call::transfer { .. }) => false,
			_ => true,
		});

		ExtBuilder::default().build().execute_with(|| {
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 10);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();
			System::reset_events();
			MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic,
			)
			.unwrap();

			let remark_hash = <Test as frame_system::Config>::Hashing::hash(b"Hello");
			assert_eq!(
				System::events(),
				vec![
					EventRecord {
						phase: Phase::Initialization,
						event: MetaEvent::System(frame_system::Event::Remarked {
							sender: BOB,
							hash: remark_hash
						}),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: MetaEvent::Utility(pallet_utility::Event::ItemCompleted),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: MetaEvent::Utility(pallet_utility::Event::BatchInterrupted {
							index: 1,
							error: frame_system::Error::<Test>::CallFiltered.into()
						},),
						topics: vec![],
					},
					EventRecord {
						phase: Phase::Initialization,
						event: MetaEvent::Contracts(crate::Event::Called {
							caller: ALICE,
							contract: BOB,
						}),
						topics: vec![hash(&ALICE), hash(&BOB)],
					},
				]
			);
		});
	}

	#[test]
	fn nonce() {
		let fail_code = MockLoader::insert(Constructor, |_, _| exec_trapped());
		let success_code = MockLoader::insert(Constructor, |_, _| exec_success());
		let succ_fail_code = MockLoader::insert(Constructor, move |ctx, _| {
			ctx.ext
				.instantiate(
					Weight::zero(),
					fail_code,
					ctx.ext.minimum_balance() * 100,
					vec![],
					&[],
				)
				.ok();
			exec_success()
		});
		let succ_succ_code = MockLoader::insert(Constructor, move |ctx, _| {
			let (account_id, _) = ctx
				.ext
				.instantiate(
					Weight::zero(),
					success_code,
					ctx.ext.minimum_balance() * 100,
					vec![],
					&[],
				)
				.unwrap();

			// a plain call should not influence the account counter
			ctx.ext.call(Weight::zero(), account_id, 0, vec![], false).unwrap();

			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			let fail_executable =
				MockExecutable::from_storage(fail_code, &schedule, &mut gas_meter).unwrap();
			let success_executable =
				MockExecutable::from_storage(success_code, &schedule, &mut gas_meter).unwrap();
			let succ_fail_executable =
				MockExecutable::from_storage(succ_fail_code, &schedule, &mut gas_meter).unwrap();
			let succ_succ_executable =
				MockExecutable::from_storage(succ_succ_code, &schedule, &mut gas_meter).unwrap();
			set_balance(&ALICE, min_balance * 1000);
			let mut storage_meter =
				storage::meter::Meter::new(&ALICE, Some(min_balance * 500), min_balance * 100)
					.unwrap();

			MockStack::run_instantiate(
				ALICE,
				fail_executable,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				min_balance * 100,
				vec![],
				&[],
				None,
			)
			.ok();
			assert_eq!(<Nonce<Test>>::get(), 0);

			assert_ok!(MockStack::run_instantiate(
				ALICE,
				success_executable,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				min_balance * 100,
				vec![],
				&[],
				None,
			));
			assert_eq!(<Nonce<Test>>::get(), 1);

			assert_ok!(MockStack::run_instantiate(
				ALICE,
				succ_fail_executable,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				min_balance * 200,
				vec![],
				&[],
				None,
			));
			assert_eq!(<Nonce<Test>>::get(), 2);

			assert_ok!(MockStack::run_instantiate(
				ALICE,
				succ_succ_executable,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				min_balance * 200,
				vec![],
				&[],
				None,
			));
			assert_eq!(<Nonce<Test>>::get(), 4);
		});
	}

	#[test]
	fn set_storage_works() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			// Write
			assert_eq!(
				ctx.ext.set_storage(&[1; 32], Some(vec![1, 2, 3]), false),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.set_storage(&[2; 32], Some(vec![4, 5, 6]), true),
				Ok(WriteOutcome::New)
			);
			assert_eq!(ctx.ext.set_storage(&[3; 32], None, false), Ok(WriteOutcome::New));
			assert_eq!(ctx.ext.set_storage(&[4; 32], None, true), Ok(WriteOutcome::New));
			assert_eq!(ctx.ext.set_storage(&[5; 32], Some(vec![]), false), Ok(WriteOutcome::New));
			assert_eq!(ctx.ext.set_storage(&[6; 32], Some(vec![]), true), Ok(WriteOutcome::New));

			// Overwrite
			assert_eq!(
				ctx.ext.set_storage(&[1; 32], Some(vec![42]), false),
				Ok(WriteOutcome::Overwritten(3))
			);
			assert_eq!(
				ctx.ext.set_storage(&[2; 32], Some(vec![48]), true),
				Ok(WriteOutcome::Taken(vec![4, 5, 6]))
			);
			assert_eq!(ctx.ext.set_storage(&[3; 32], None, false), Ok(WriteOutcome::New));
			assert_eq!(ctx.ext.set_storage(&[4; 32], None, true), Ok(WriteOutcome::New));
			assert_eq!(
				ctx.ext.set_storage(&[5; 32], Some(vec![]), false),
				Ok(WriteOutcome::Overwritten(0))
			);
			assert_eq!(
				ctx.ext.set_storage(&[6; 32], Some(vec![]), true),
				Ok(WriteOutcome::Taken(vec![]))
			);

			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 1000);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, None, 0).unwrap();
			assert_ok!(MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic
			));
		});
	}

	#[test]
	fn set_storage_transparent_works() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			// Write
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([1; 64].to_vec()).unwrap(),
					Some(vec![1, 2, 3]),
					false
				),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([2; 19].to_vec()).unwrap(),
					Some(vec![4, 5, 6]),
					true
				),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([3; 19].to_vec()).unwrap(),
					None,
					false
				),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([4; 64].to_vec()).unwrap(),
					None,
					true
				),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([5; 30].to_vec()).unwrap(),
					Some(vec![]),
					false
				),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([6; 128].to_vec()).unwrap(),
					Some(vec![]),
					true
				),
				Ok(WriteOutcome::New)
			);

			// Overwrite
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([1; 64].to_vec()).unwrap(),
					Some(vec![42, 43, 44]),
					false
				),
				Ok(WriteOutcome::Overwritten(3))
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([2; 19].to_vec()).unwrap(),
					Some(vec![48]),
					true
				),
				Ok(WriteOutcome::Taken(vec![4, 5, 6]))
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([3; 19].to_vec()).unwrap(),
					None,
					false
				),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([4; 64].to_vec()).unwrap(),
					None,
					true
				),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([5; 30].to_vec()).unwrap(),
					Some(vec![]),
					false
				),
				Ok(WriteOutcome::Overwritten(0))
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([6; 128].to_vec()).unwrap(),
					Some(vec![]),
					true
				),
				Ok(WriteOutcome::Taken(vec![]))
			);

			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 1000);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, None, 0).unwrap();
			assert_ok!(MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic
			));
		});
	}

	#[test]
	fn get_storage_works() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			assert_eq!(
				ctx.ext.set_storage(&[1; 32], Some(vec![1, 2, 3]), false),
				Ok(WriteOutcome::New)
			);
			assert_eq!(ctx.ext.set_storage(&[2; 32], Some(vec![]), false), Ok(WriteOutcome::New));
			assert_eq!(ctx.ext.get_storage(&[1; 32]), Some(vec![1, 2, 3]));
			assert_eq!(ctx.ext.get_storage(&[2; 32]), Some(vec![]));
			assert_eq!(ctx.ext.get_storage(&[3; 32]), None);

			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 1000);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, None, 0).unwrap();
			assert_ok!(MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic
			));
		});
	}

	#[test]
	fn get_storage_size_works() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			assert_eq!(
				ctx.ext.set_storage(&[1; 32], Some(vec![1, 2, 3]), false),
				Ok(WriteOutcome::New)
			);
			assert_eq!(ctx.ext.set_storage(&[2; 32], Some(vec![]), false), Ok(WriteOutcome::New));
			assert_eq!(ctx.ext.get_storage_size(&[1; 32]), Some(3));
			assert_eq!(ctx.ext.get_storage_size(&[2; 32]), Some(0));
			assert_eq!(ctx.ext.get_storage_size(&[3; 32]), None);

			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 1000);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, None, 0).unwrap();
			assert_ok!(MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic
			));
		});
	}

	#[test]
	fn get_storage_transparent_works() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([1; 19].to_vec()).unwrap(),
					Some(vec![1, 2, 3]),
					false
				),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([2; 16].to_vec()).unwrap(),
					Some(vec![]),
					false
				),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.get_storage_transparent(
					&VarSizedKey::<Test>::try_from([1; 19].to_vec()).unwrap()
				),
				Some(vec![1, 2, 3])
			);
			assert_eq!(
				ctx.ext.get_storage_transparent(
					&VarSizedKey::<Test>::try_from([2; 16].to_vec()).unwrap()
				),
				Some(vec![])
			);
			assert_eq!(
				ctx.ext.get_storage_transparent(
					&VarSizedKey::<Test>::try_from([3; 8].to_vec()).unwrap()
				),
				None
			);

			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 1000);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, None, 0).unwrap();
			assert_ok!(MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic
			));
		});
	}

	#[test]
	fn get_storage_size_transparent_works() {
		let code_hash = MockLoader::insert(Call, |ctx, _| {
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([1; 19].to_vec()).unwrap(),
					Some(vec![1, 2, 3]),
					false
				),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.set_storage_transparent(
					&VarSizedKey::<Test>::try_from([2; 16].to_vec()).unwrap(),
					Some(vec![]),
					false
				),
				Ok(WriteOutcome::New)
			);
			assert_eq!(
				ctx.ext.get_storage_size_transparent(
					&VarSizedKey::<Test>::try_from([1; 19].to_vec()).unwrap()
				),
				Some(3)
			);
			assert_eq!(
				ctx.ext.get_storage_size_transparent(
					&VarSizedKey::<Test>::try_from([2; 16].to_vec()).unwrap()
				),
				Some(0)
			);
			assert_eq!(
				ctx.ext.get_storage_size_transparent(
					&VarSizedKey::<Test>::try_from([3; 8].to_vec()).unwrap()
				),
				None
			);

			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 1000);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, None, 0).unwrap();
			assert_ok!(MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic
			));
		});
	}

	#[test]
	fn ecdsa_to_eth_address_returns_proper_value() {
		let bob_ch = MockLoader::insert(Call, |ctx, _| {
			let pubkey_compressed = array_bytes::hex2array_unchecked(
				"028db55b05db86c0b1786ca49f095d76344c9e6056b2f02701a7e7f3c20aabfd91",
			);
			assert_eq!(
				ctx.ext.ecdsa_to_eth_address(&pubkey_compressed).unwrap(),
				array_bytes::hex2array_unchecked::<20>("09231da7b19A016f9e576d23B16277062F4d46A8")
			);
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let schedule = <Test as Config>::Schedule::get();
			place_contract(&BOB, bob_ch);

			let mut storage_meter = storage::meter::Meter::new(&ALICE, Some(0), 0).unwrap();
			let result = MockStack::run_call(
				ALICE,
				BOB,
				&mut GasMeter::<Test>::new(GAS_LIMIT),
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic,
			);
			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn nonce_api_works() {
		let fail_code = MockLoader::insert(Constructor, |_, _| exec_trapped());
		let success_code = MockLoader::insert(Constructor, |_, _| exec_success());
		let code_hash = MockLoader::insert(Call, move |ctx, _| {
			// It is set to one when this contract was instantiated by `place_contract`
			assert_eq!(ctx.ext.nonce(), 1);
			// Should not change without any instantation in-between
			assert_eq!(ctx.ext.nonce(), 1);
			// Should not change with a failed instantiation
			assert_err!(
				ctx.ext.instantiate(Weight::zero(), fail_code, 0, vec![], &[],),
				ExecError {
					error: <Error<Test>>::ContractTrapped.into(),
					origin: ErrorOrigin::Callee
				}
			);
			assert_eq!(ctx.ext.nonce(), 1);
			// Successful instantation increments
			ctx.ext.instantiate(Weight::zero(), success_code, 0, vec![], &[]).unwrap();
			assert_eq!(ctx.ext.nonce(), 2);
			exec_success()
		});

		ExtBuilder::default().build().execute_with(|| {
			let min_balance = <Test as Config>::Currency::minimum_balance();
			let schedule = <Test as Config>::Schedule::get();
			let mut gas_meter = GasMeter::<Test>::new(GAS_LIMIT);
			set_balance(&ALICE, min_balance * 1000);
			place_contract(&BOB, code_hash);
			let mut storage_meter = storage::meter::Meter::new(&ALICE, None, 0).unwrap();
			assert_ok!(MockStack::run_call(
				ALICE,
				BOB,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				0,
				vec![],
				None,
				Determinism::Deterministic
			));
		});
	}
}
