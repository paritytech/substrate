// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

use super::{CodeHash, Config, ContractAddressFor, Event, RawEvent, Trait,
	TrieId, BalanceOf, ContractInfo};
use crate::account_db::{AccountDb, DirectAccountDb, OverlayAccountDb};
use crate::gas::{Gas, GasMeter, Token, approx_gas_for_balance};
use crate::rent;

use rstd::prelude::*;
use sr_primitives::traits::{Bounded, CheckedAdd, CheckedSub, Zero};
use support::traits::{WithdrawReason, Currency, Time, Randomness};

pub type AccountIdOf<T> = <T as system::Trait>::AccountId;
pub type CallOf<T> = <T as Trait>::Call;
pub type MomentOf<T> = <<T as Trait>::Time as Time>::Moment;
pub type SeedOf<T> = <T as system::Trait>::Hash;
pub type BlockNumberOf<T> = <T as system::Trait>::BlockNumber;
pub type StorageKey = [u8; 32];

/// A type that represents a topic of an event. At the moment a hash is used.
pub type TopicOf<T> = <T as system::Trait>::Hash;

/// A status code return to the source of a contract call or instantiation indicating success or
/// failure. A code of 0 indicates success and that changes are applied. All other codes indicate
/// failure and that changes are reverted. The particular code in the case of failure is opaque and
/// may be interpreted by the calling contract.
pub type StatusCode = u8;

/// The status code indicating success.
pub const STATUS_SUCCESS: StatusCode = 0;

/// Output of a contract call or instantiation which ran to completion.
#[cfg_attr(test, derive(PartialEq, Eq, Debug))]
pub struct ExecReturnValue {
	pub status: StatusCode,
	pub data: Vec<u8>,
}

impl ExecReturnValue {
	/// Returns whether the call or instantiation exited with a successful status code.
	pub fn is_success(&self) -> bool {
		self.status == STATUS_SUCCESS
	}
}

/// An error indicating some failure to execute a contract call or instantiation. This can include
/// VM-specific errors during execution (eg. division by 0, OOB access, failure to satisfy some
/// precondition of a system call, etc.) or errors with the orchestration (eg. out-of-gas errors, a
/// non-existent destination contract, etc.).
#[cfg_attr(test, derive(sr_primitives::RuntimeDebug))]
pub struct ExecError {
	pub reason: &'static str,
	/// This is an allocated buffer that may be reused. The buffer must be cleared explicitly
	/// before reuse.
	pub buffer: Vec<u8>,
}

pub type ExecResult = Result<ExecReturnValue, ExecError>;

/// Evaluate an expression of type Result<_, &'static str> and either resolve to the value if Ok or
/// wrap the error string into an ExecutionError with the provided buffer and return from the
/// enclosing function. This macro is used instead of .map_err(..)? in order to avoid taking
/// ownership of buffer unless there is an error.
#[macro_export]
macro_rules! try_or_exec_error {
	($e:expr, $buffer:expr) => {
		match $e {
			Ok(val) => val,
			Err(reason) => return Err($crate::exec::ExecError { reason, buffer: $buffer }),
		}
	}
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
	/// the storage entry is deleted. Returns an Err if the value size is too large.
	fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>) -> Result<(), &'static str>;

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

	/// Call (possibly transferring some amount of funds) into the specified account.
	fn call(
		&mut self,
		to: &AccountIdOf<Self::T>,
		value: BalanceOf<Self::T>,
		gas_meter: &mut GasMeter<Self::T>,
		input_data: Vec<u8>,
	) -> ExecResult;

	/// Notes a call dispatch.
	fn note_dispatch_call(&mut self, call: CallOf<Self::T>);

	/// Notes a restoration request.
	fn note_restore_to(
		&mut self,
		dest: AccountIdOf<Self::T>,
		code_hash: CodeHash<Self::T>,
		rent_allowance: BalanceOf<Self::T>,
		delta: Vec<StorageKey>,
	);

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

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub enum ExecFeeToken {
	/// Base fee charged for a call.
	Call,
	/// Base fee charged for a instantiate.
	Instantiate,
}

impl<T: Trait> Token<T> for ExecFeeToken {
	type Metadata = Config<T>;
	#[inline]
	fn calculate_amount(&self, metadata: &Config<T>) -> Gas {
		match *self {
			ExecFeeToken::Call => metadata.schedule.call_base_cost,
			ExecFeeToken::Instantiate => metadata.schedule.instantiate_base_cost,
		}
	}
}

#[cfg_attr(any(feature = "std", test), derive(PartialEq, Eq, Clone))]
#[derive(sr_primitives::RuntimeDebug)]
pub enum DeferredAction<T: Trait> {
	DepositEvent {
		/// A list of topics this event will be deposited with.
		topics: Vec<T::Hash>,
		/// The event to deposit.
		event: Event<T>,
	},
	DispatchRuntimeCall {
		/// The account id of the contract who dispatched this call.
		origin: T::AccountId,
		/// The call to dispatch.
		call: <T as Trait>::Call,
	},
	RestoreTo {
		/// The account id of the contract which is removed during the restoration and transfers
		/// its storage to the restored contract.
		donor: T::AccountId,
		/// The account id of the restored contract.
		dest: T::AccountId,
		/// The code hash of the restored contract.
		code_hash: CodeHash<T>,
		/// The initial rent allowance to set.
		rent_allowance: BalanceOf<T>,
		/// The keys to delete upon restoration.
		delta: Vec<StorageKey>,
	},
}

pub struct ExecutionContext<'a, T: Trait + 'a, V, L> {
	pub parent: Option<&'a ExecutionContext<'a, T, V, L>>,
	pub self_account: T::AccountId,
	pub self_trie_id: Option<TrieId>,
	pub overlay: OverlayAccountDb<'a, T>,
	pub depth: usize,
	pub deferred: Vec<DeferredAction<T>>,
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
			parent: None,
			self_trie_id: None,
			self_account: origin,
			overlay: OverlayAccountDb::<T>::new(&DirectAccountDb),
			depth: 0,
			deferred: Vec::new(),
			config: &cfg,
			vm: &vm,
			loader: &loader,
			timestamp: T::Time::now(),
			block_number: <system::Module<T>>::block_number(),
		}
	}

	fn nested<'b, 'c: 'b>(&'c self, dest: T::AccountId, trie_id: Option<TrieId>)
		-> ExecutionContext<'b, T, V, L>
	{
		ExecutionContext {
			parent: Some(self),
			self_trie_id: trie_id,
			self_account: dest,
			overlay: OverlayAccountDb::new(&self.overlay),
			depth: self.depth + 1,
			deferred: Vec::new(),
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
			return Err(ExecError {
				reason: "reached maximum depth, cannot make a call",
				buffer: input_data,
			});
		}

		if gas_meter
			.charge(self.config, ExecFeeToken::Call)
			.is_out_of_gas()
		{
			return Err(ExecError {
				reason: "not enough gas to pay base call fee",
				buffer: input_data,
			});
		}

		// Assumption: pay_rent doesn't collide with overlay because
		// pay_rent will be done on first call and dest contract and balance
		// cannot be changed before the first call
		let contract_info = rent::pay_rent::<T>(&dest);

		// Calls to dead contracts always fail.
		if let Some(ContractInfo::Tombstone(_)) = contract_info {
			return Err(ExecError {
				reason: "contract has been evicted",
				buffer: input_data,
			});
		};

		let caller = self.self_account.clone();
		let dest_trie_id = contract_info.and_then(|i| i.as_alive().map(|i| i.trie_id.clone()));

		self.with_nested_context(dest.clone(), dest_trie_id, |nested| {
			if value > BalanceOf::<T>::zero() {
				try_or_exec_error!(
					transfer(
						gas_meter,
						TransferCause::Call,
						&caller,
						&dest,
						value,
						nested,
					),
					input_data
				);
			}

			// If code_hash is not none, then the destination account is a live contract, otherwise
			// it is a regular account since tombstone accounts have already been rejected.
			match nested.overlay.get_code_hash(&dest) {
				Some(dest_code_hash) => {
					let executable = try_or_exec_error!(
						nested.loader.load_main(&dest_code_hash),
						input_data
					);
					let output = nested.vm
						.execute(
							&executable,
							nested.new_call_context(caller, value),
							input_data,
							gas_meter,
						)?;

					// Destroy contract if insufficient remaining balance.
					if nested.overlay.get_balance(&dest) < nested.config.existential_deposit {
						let parent = nested.parent
							.expect("a nested execution context must have a parent; qed");
						if parent.is_live(&dest) {
							return Err(ExecError {
								reason: "contract cannot be destroyed during recursive execution",
								buffer: output.data,
							});
						}

						nested.overlay.destroy_contract(&dest);
					}

					Ok(output)
				}
				None => Ok(ExecReturnValue { status: STATUS_SUCCESS, data: Vec::new() }),
			}
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
			return Err(ExecError {
				reason: "reached maximum depth, cannot instantiate",
				buffer: input_data,
			});
		}

		if gas_meter
			.charge(self.config, ExecFeeToken::Instantiate)
			.is_out_of_gas()
		{
			return Err(ExecError {
				reason: "not enough gas to pay base instantiate fee",
				buffer: input_data,
			});
		}

		let caller = self.self_account.clone();
		let dest = T::DetermineContractAddress::contract_address_for(
			code_hash,
			&input_data,
			&caller,
		);

		// TrieId has not been generated yet and storage is empty since contract is new.
		let dest_trie_id = None;

		let output = self.with_nested_context(dest.clone(), dest_trie_id, |nested| {
			try_or_exec_error!(
				nested.overlay.instantiate_contract(&dest, code_hash.clone()),
				input_data
			);

			// Send funds unconditionally here. If the `endowment` is below existential_deposit
			// then error will be returned here.
			try_or_exec_error!(
				transfer(
					gas_meter,
					TransferCause::Instantiate,
					&caller,
					&dest,
					endowment,
					nested,
				),
				input_data
			);

			let executable = try_or_exec_error!(
				nested.loader.load_init(&code_hash),
				input_data
			);
			let output = nested.vm
				.execute(
					&executable,
					nested.new_call_context(caller.clone(), endowment),
					input_data,
					gas_meter,
				)?;

			// Error out if insufficient remaining balance.
			if nested.overlay.get_balance(&dest) < nested.config.existential_deposit {
				return Err(ExecError {
					reason: "insufficient remaining balance",
					buffer: output.data,
				});
			}

			// Deposit an instantiation event.
			nested.deferred.push(DeferredAction::DepositEvent {
				event: RawEvent::Instantiated(caller.clone(), dest.clone()),
				topics: Vec::new(),
			});

			Ok(output)
		})?;

		Ok((dest, output))
	}

	fn new_call_context<'b>(&'b mut self, caller: T::AccountId, value: BalanceOf<T>)
		-> CallContext<'b, 'a, T, V, L>
	{
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

	fn with_nested_context<F>(&mut self, dest: T::AccountId, trie_id: Option<TrieId>, func: F)
		-> ExecResult
		where F: FnOnce(&mut ExecutionContext<T, V, L>) -> ExecResult
	{
		let (output, change_set, deferred) = {
			let mut nested = self.nested(dest, trie_id);
			let output = func(&mut nested)?;
			(output, nested.overlay.into_change_set(), nested.deferred)
		};

		if output.is_success() {
			self.overlay.commit(change_set);
			self.deferred.extend(deferred);
		}

		Ok(output)
	}

	/// Returns whether a contract, identified by address, is currently live in the execution
	/// stack, meaning it is in the middle of an execution.
	fn is_live(&self, account: &T::AccountId) -> bool {
		&self.self_account == account ||
			self.parent.map_or(false, |parent| parent.is_live(account))
	}
}

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub enum TransferFeeKind {
	ContractInstantiate,
	AccountCreate,
	Transfer,
}

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub struct TransferFeeToken<Balance> {
	kind: TransferFeeKind,
	gas_price: Balance,
}

impl<T: Trait> Token<T> for TransferFeeToken<BalanceOf<T>> {
	type Metadata = Config<T>;

	#[inline]
	fn calculate_amount(&self, metadata: &Config<T>) -> Gas {
		let balance_fee = match self.kind {
			TransferFeeKind::ContractInstantiate => metadata.contract_account_instantiate_fee,
			TransferFeeKind::AccountCreate => metadata.account_create_fee,
			TransferFeeKind::Transfer => metadata.transfer_fee,
		};
		approx_gas_for_balance(self.gas_price, balance_fee)
	}
}

/// Describes possible transfer causes.
enum TransferCause {
	Call,
	Instantiate,
}

/// Transfer some funds from `transactor` to `dest`.
///
/// All balance changes are performed in the `overlay`.
///
/// This function also handles charging the fee. The fee depends
/// on whether the transfer happening because of contract instantiation
/// (transferring endowment) or because of a transfer via `call`. This
/// is specified using the `cause` parameter.
///
/// NOTE: that the fee is denominated in `BalanceOf<T>` units, but
/// charged in `Gas` from the provided `gas_meter`. This means
/// that the actual amount charged might differ.
///
/// NOTE: that we allow for draining all funds of the contract so it
/// can go below existential deposit, essentially giving a contract
/// the chance to give up it's life.
fn transfer<'a, T: Trait, V: Vm<T>, L: Loader<T>>(
	gas_meter: &mut GasMeter<T>,
	cause: TransferCause,
	transactor: &T::AccountId,
	dest: &T::AccountId,
	value: BalanceOf<T>,
	ctx: &mut ExecutionContext<'a, T, V, L>,
) -> Result<(), &'static str> {
	use self::TransferCause::*;
	use self::TransferFeeKind::*;

	let to_balance = ctx.overlay.get_balance(dest);

	// `would_create` indicates whether the account will be created if this transfer gets executed.
	// This flag is orthogonal to `cause.
	// For example, we can instantiate a contract at the address which already has some funds. In this
	// `would_create` will be `false`. Another example would be when this function is called from `call`,
	// and account with the address `dest` doesn't exist yet `would_create` will be `true`.
	let would_create = to_balance.is_zero();

	let token = {
		let kind: TransferFeeKind = match cause {
			// If this function is called from `Instantiate` routine, then we always
			// charge contract account creation fee.
			Instantiate => ContractInstantiate,

			// Otherwise the fee depends on whether we create a new account or transfer
			// to an existing one.
			Call => if would_create {
				TransferFeeKind::AccountCreate
			} else {
				TransferFeeKind::Transfer
			},
		};
		TransferFeeToken {
			kind,
			gas_price: gas_meter.gas_price(),
		}
	};

	if gas_meter.charge(ctx.config, token).is_out_of_gas() {
		return Err("not enough gas to pay transfer fee");
	}

	// We allow balance to go below the existential deposit here:
	let from_balance = ctx.overlay.get_balance(transactor);
	let new_from_balance = match from_balance.checked_sub(&value) {
		Some(b) => b,
		None => return Err("balance too low to send value"),
	};
	if would_create && value < ctx.config.existential_deposit {
		return Err("value too low to create account");
	}
	T::Currency::ensure_can_withdraw(transactor, value, WithdrawReason::Transfer.into(), new_from_balance)?;

	let new_to_balance = match to_balance.checked_add(&value) {
		Some(b) => b,
		None => return Err("destination balance too high to receive value"),
	};

	if transactor != dest {
		ctx.overlay.set_balance(transactor, new_from_balance);
		ctx.overlay.set_balance(dest, new_to_balance);
		ctx.deferred.push(DeferredAction::DepositEvent {
			event: RawEvent::Transfer(transactor.clone(), dest.clone(), value),
			topics: Vec::new(),
		});
	}

	Ok(())
}

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
		self.ctx.overlay.get_storage(&self.ctx.self_account, self.ctx.self_trie_id.as_ref(), key)
	}

	fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>) -> Result<(), &'static str> {
		if let Some(ref value) = value {
			if self.max_value_size() < value.len() as u32 {
				return Err("value size exceeds maximum");
			}
		}

		self.ctx
			.overlay
			.set_storage(&self.ctx.self_account, key, value);
		Ok(())
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

	fn call(
		&mut self,
		to: &T::AccountId,
		value: BalanceOf<T>,
		gas_meter: &mut GasMeter<T>,
		input_data: Vec<u8>,
	) -> ExecResult {
		self.ctx.call(to.clone(), value, gas_meter, input_data)
	}

	fn note_dispatch_call(&mut self, call: CallOf<Self::T>) {
		self.ctx.deferred.push(DeferredAction::DispatchRuntimeCall {
			origin: self.ctx.self_account.clone(),
			call,
		});
	}

	fn note_restore_to(
		&mut self,
		dest: AccountIdOf<Self::T>,
		code_hash: CodeHash<Self::T>,
		rent_allowance: BalanceOf<Self::T>,
		delta: Vec<StorageKey>,
	) {
		self.ctx.deferred.push(DeferredAction::RestoreTo {
			donor: self.ctx.self_account.clone(),
			dest,
			code_hash,
			rent_allowance,
			delta,
		});
	}

	fn address(&self) -> &T::AccountId {
		&self.ctx.self_account
	}

	fn caller(&self) -> &T::AccountId {
		&self.caller
	}

	fn balance(&self) -> BalanceOf<T> {
		self.ctx.overlay.get_balance(&self.ctx.self_account)
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

	fn deposit_event(&mut self, topics: Vec<T::Hash>, data: Vec<u8>) {
		self.ctx.deferred.push(DeferredAction::DepositEvent {
			topics,
			event: RawEvent::Contract(self.ctx.self_account.clone(), data),
		});
	}

	fn set_rent_allowance(&mut self, rent_allowance: BalanceOf<T>) {
		self.ctx.overlay.set_rent_allowance(&self.ctx.self_account, rent_allowance)
	}

	fn rent_allowance(&self) -> BalanceOf<T> {
		self.ctx.overlay.get_rent_allowance(&self.ctx.self_account)
			.unwrap_or(<BalanceOf<T>>::max_value()) // Must never be triggered actually
	}

	fn block_number(&self) -> T::BlockNumber { self.block_number }

	fn max_value_size(&self) -> u32 {
		self.ctx.config.max_value_size
	}
}

/// These tests exercise the executive layer.
///
/// In these tests the VM/loader are mocked. Instead of dealing with wasm bytecode they use simple closures.
/// This allows you to tackle executive logic more thoroughly without writing a
/// wasm VM code.
///
/// Because it's the executive layer:
///
/// - no gas meter setup and teardown logic. All balances are *AFTER* gas purchase.
/// - executive layer doesn't alter any storage!
#[cfg(test)]
mod tests {
	use super::{
		BalanceOf, ExecFeeToken, ExecutionContext, Ext, Loader, TransferFeeKind, TransferFeeToken,
		Vm, ExecResult, RawEvent, DeferredAction,
	};
	use crate::{
		account_db::AccountDb, gas::GasMeter, tests::{ExtBuilder, Test},
		exec::{ExecReturnValue, ExecError, STATUS_SUCCESS}, CodeHash, Config,
	};
	use std::{cell::RefCell, rc::Rc, collections::HashMap, marker::PhantomData};
	use assert_matches::assert_matches;

	const ALICE: u64 = 1;
	const BOB: u64 = 2;
	const CHARLIE: u64 = 3;

	impl<'a, T, V, L> ExecutionContext<'a, T, V, L>
		where T: crate::Trait
	{
		fn events(&self) -> Vec<DeferredAction<T>> {
			self.deferred
				.iter()
				.filter(|action| match *action {
					DeferredAction::DepositEvent { .. } => true,
					_ => false,
				})
				.cloned()
				.collect()
		}
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
			let code_hash = <Test as system::Trait>::Hash::from_low_u64_be(self.counter);

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
		Ok(ExecReturnValue { status: STATUS_SUCCESS, data: Vec::new() })
	}

	#[test]
	fn it_works() {
		let value = Default::default();
		let mut gas_meter = GasMeter::<Test>::with_limit(10000, 1);
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
			ctx.overlay.instantiate_contract(&BOB, exec_ch).unwrap();

			assert_matches!(
				ctx.call(BOB, value, &mut gas_meter, data),
				Ok(_)
			);
		});

		assert_eq!(&*test_data.borrow(), &vec![0, 1]);
	}

	#[test]
	fn base_fees() {
		let origin = ALICE;
		let dest = BOB;

		// This test verifies that base fee for call is taken.
		ExtBuilder::default().build().execute_with(|| {
			let vm = MockVm::new();
			let loader = MockLoader::empty();
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			ctx.overlay.set_balance(&origin, 100);
			ctx.overlay.set_balance(&dest, 0);

			let mut gas_meter = GasMeter::<Test>::with_limit(1000, 1);

			let result = ctx.call(dest, 0, &mut gas_meter, vec![]);
			assert_matches!(result, Ok(_));

			let mut toks = gas_meter.tokens().iter();
			match_tokens!(toks, ExecFeeToken::Call,);
		});

		// This test verifies that base fee for instantiation is taken.
		ExtBuilder::default().build().execute_with(|| {
			let mut loader = MockLoader::empty();
			let code = loader.insert(|_| exec_success());

			let vm = MockVm::new();
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);

			ctx.overlay.set_balance(&origin, 100);

			let mut gas_meter = GasMeter::<Test>::with_limit(1000, 1);

			let result = ctx.instantiate(0, &mut gas_meter, &code, vec![]);
			assert_matches!(result, Ok(_));

			let mut toks = gas_meter.tokens().iter();
			match_tokens!(toks, ExecFeeToken::Instantiate,);
		});
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
			ctx.overlay.set_balance(&origin, 100);
			ctx.overlay.set_balance(&dest, 0);

			let output = ctx.call(
				dest,
				55,
				&mut GasMeter::<Test>::with_limit(1000, 1),
				vec![],
			).unwrap();

			assert!(output.is_success());
			assert_eq!(ctx.overlay.get_balance(&origin), 45);
			assert_eq!(ctx.overlay.get_balance(&dest), 55);
		});
	}

	#[test]
	fn changes_are_reverted_on_failing_call() {
		// This test verifies that a contract is able to transfer
		// some funds to another account.
		let origin = ALICE;
		let dest = BOB;

		let vm = MockVm::new();
		let mut loader = MockLoader::empty();
		let return_ch = loader.insert(
			|_| Ok(ExecReturnValue { status: 1, data: Vec::new() })
		);

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			ctx.overlay.instantiate_contract(&BOB, return_ch).unwrap();
			ctx.overlay.set_balance(&origin, 100);
			ctx.overlay.set_balance(&dest, 0);

			let output = ctx.call(
				dest,
				55,
				&mut GasMeter::<Test>::with_limit(1000, 1),
				vec![],
			).unwrap();

			assert!(!output.is_success());
			assert_eq!(ctx.overlay.get_balance(&origin), 100);
			assert_eq!(ctx.overlay.get_balance(&dest), 0);
		});
	}

	#[test]
	fn transfer_fees() {
		let origin = ALICE;
		let dest = BOB;

		// This test sends 50 units of currency to a non-existent account.
		// This should lead to creation of a new account thus
		// a fee should be charged.
		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let vm = MockVm::new();
			let loader = MockLoader::empty();
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			ctx.overlay.set_balance(&origin, 100);
			ctx.overlay.set_balance(&dest, 0);

			let mut gas_meter = GasMeter::<Test>::with_limit(1000, 1);

			let result = ctx.call(dest, 50, &mut gas_meter, vec![]);
			assert_matches!(result, Ok(_));

			let mut toks = gas_meter.tokens().iter();
			match_tokens!(
				toks,
				ExecFeeToken::Call,
				TransferFeeToken {
					kind: TransferFeeKind::AccountCreate,
					gas_price: 1u64
				},
			);
		});

		// This one is similar to the previous one but transfer to an existing account.
		// In this test we expect that a regular transfer fee is charged.
		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let vm = MockVm::new();
			let loader = MockLoader::empty();
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			ctx.overlay.set_balance(&origin, 100);
			ctx.overlay.set_balance(&dest, 15);

			let mut gas_meter = GasMeter::<Test>::with_limit(1000, 1);

			let result = ctx.call(dest, 50, &mut gas_meter, vec![]);
			assert_matches!(result, Ok(_));

			let mut toks = gas_meter.tokens().iter();
			match_tokens!(
				toks,
				ExecFeeToken::Call,
				TransferFeeToken {
					kind: TransferFeeKind::Transfer,
					gas_price: 1u64
				},
			);
		});

		// This test sends 50 units of currency as an endownment to a newly
		// instantiated contract.
		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let mut loader = MockLoader::empty();
			let code = loader.insert(|_| exec_success());

			let vm = MockVm::new();
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);

			ctx.overlay.set_balance(&origin, 100);
			ctx.overlay.set_balance(&dest, 15);

			let mut gas_meter = GasMeter::<Test>::with_limit(1000, 1);

			let result = ctx.instantiate(50, &mut gas_meter, &code, vec![]);
			assert_matches!(result, Ok(_));

			let mut toks = gas_meter.tokens().iter();
			match_tokens!(
				toks,
				ExecFeeToken::Instantiate,
				TransferFeeToken {
					kind: TransferFeeKind::ContractInstantiate,
					gas_price: 1u64
				},
			);
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
			ctx.overlay.set_balance(&origin, 0);

			let result = ctx.call(
				dest,
				100,
				&mut GasMeter::<Test>::with_limit(1000, 1),
				vec![],
			);

			assert_matches!(
				result,
				Err(ExecError { reason: "balance too low to send value", buffer: _ })
			);
			assert_eq!(ctx.overlay.get_balance(&origin), 0);
			assert_eq!(ctx.overlay.get_balance(&dest), 0);
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
			|_| Ok(ExecReturnValue { status: STATUS_SUCCESS, data: vec![1, 2, 3, 4] })
		);

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			ctx.overlay.instantiate_contract(&BOB, return_ch).unwrap();

			let result = ctx.call(
				dest,
				0,
				&mut GasMeter::<Test>::with_limit(1000, 1),
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
			|_| Ok(ExecReturnValue { status: 1, data: vec![1, 2, 3, 4] })
		);

		ExtBuilder::default().build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			ctx.overlay.instantiate_contract(&BOB, return_ch).unwrap();

			let result = ctx.call(
				dest,
				0,
				&mut GasMeter::<Test>::with_limit(1000, 1),
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
			ctx.overlay.instantiate_contract(&BOB, input_data_ch).unwrap();

			let result = ctx.call(
				BOB,
				0,
				&mut GasMeter::<Test>::with_limit(10000, 1),
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

			let result = ctx.instantiate(
				0,
				&mut GasMeter::<Test>::with_limit(10000, 1),
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
				assert_matches!(
					r,
					Err(ExecError { reason: "reached maximum depth, cannot make a call", buffer: _ })
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
			ctx.overlay.instantiate_contract(&BOB, recurse_ch).unwrap();

			let result = ctx.call(
				BOB,
				value,
				&mut GasMeter::<Test>::with_limit(100000, 1),
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
			ctx.overlay.instantiate_contract(&dest, bob_ch).unwrap();
			ctx.overlay.instantiate_contract(&CHARLIE, charlie_ch).unwrap();

			let result = ctx.call(
				dest,
				0,
				&mut GasMeter::<Test>::with_limit(10000, 1),
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
			ctx.overlay.instantiate_contract(&BOB, bob_ch).unwrap();
			ctx.overlay.instantiate_contract(&CHARLIE, charlie_ch).unwrap();

			let result = ctx.call(
				BOB,
				0,
				&mut GasMeter::<Test>::with_limit(10000, 1),
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
					&mut GasMeter::<Test>::with_limit(10000, 1),
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
			|_| Ok(ExecReturnValue { status: STATUS_SUCCESS, data: vec![80, 65, 83, 83] })
		);

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			ctx.overlay.set_balance(&ALICE, 1000);

			let instantiated_contract_address = assert_matches!(
				ctx.instantiate(
					100,
					&mut GasMeter::<Test>::with_limit(10000, 1),
					&dummy_ch,
					vec![],
				),
				Ok((address, ref output)) if output.data == vec![80, 65, 83, 83] => address
			);

			// Check that the newly created account has the expected code hash and
			// there are instantiation event.
			assert_eq!(ctx.overlay.get_code_hash(&instantiated_contract_address).unwrap(), dummy_ch);
			assert_eq!(&ctx.events(), &[
				DeferredAction::DepositEvent {
					event: RawEvent::Transfer(ALICE, instantiated_contract_address, 100),
					topics: Vec::new(),
				},
				DeferredAction::DepositEvent {
					event: RawEvent::Instantiated(ALICE, instantiated_contract_address),
					topics: Vec::new(),
				}
			]);
		});
	}

	#[test]
	fn instantiation_fails_with_failing_output() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let dummy_ch = loader.insert(
			|_| Ok(ExecReturnValue { status: 1, data: vec![70, 65, 73, 76] })
		);

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			ctx.overlay.set_balance(&ALICE, 1000);

			let instantiated_contract_address = assert_matches!(
				ctx.instantiate(
					100,
					&mut GasMeter::<Test>::with_limit(10000, 1),
					&dummy_ch,
					vec![],
				),
				Ok((address, ref output)) if output.data == vec![70, 65, 73, 76] => address
			);

			// Check that the account has not been created.
			assert!(ctx.overlay.get_code_hash(&instantiated_contract_address).is_none());
			assert!(ctx.events().is_empty());
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
					15u64,
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
			ctx.overlay.set_balance(&ALICE, 1000);
			ctx.overlay.instantiate_contract(&BOB, instantiator_ch).unwrap();

			assert_matches!(
				ctx.call(BOB, 20, &mut GasMeter::<Test>::with_limit(1000, 1), vec![]),
				Ok(_)
			);

			let instantiated_contract_address = instantiated_contract_address.borrow().as_ref().unwrap().clone();

			// Check that the newly created account has the expected code hash and
			// there are instantiation event.
			assert_eq!(ctx.overlay.get_code_hash(&instantiated_contract_address).unwrap(), dummy_ch);
			assert_eq!(&ctx.events(), &[
				DeferredAction::DepositEvent {
					event: RawEvent::Transfer(ALICE, BOB, 20),
					topics: Vec::new(),
				},
				DeferredAction::DepositEvent {
					event: RawEvent::Transfer(BOB, instantiated_contract_address, 15),
					topics: Vec::new(),
				},
				DeferredAction::DepositEvent {
					event: RawEvent::Instantiated(BOB, instantiated_contract_address),
					topics: Vec::new(),
				},
			]);
		});
	}

	#[test]
	fn instantiation_traps() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let dummy_ch = loader.insert(
			|_| Err(ExecError { reason: "It's a trap!", buffer: Vec::new() })
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
					Err(ExecError { reason: "It's a trap!", buffer: _ })
				);

				exec_success()
			}
		});

		ExtBuilder::default().existential_deposit(15).build().execute_with(|| {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			ctx.overlay.set_balance(&ALICE, 1000);
			ctx.overlay.instantiate_contract(&BOB, instantiator_ch).unwrap();

			assert_matches!(
				ctx.call(BOB, 20, &mut GasMeter::<Test>::with_limit(1000, 1), vec![]),
				Ok(_)
			);

			// The contract wasn't instantiated so we don't expect to see an instantiation
			// event here.
			assert_eq!(&ctx.events(), &[
				DeferredAction::DepositEvent {
					event: RawEvent::Transfer(ALICE, BOB, 20),
					topics: Vec::new(),
				},
			]);
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

			let result = ctx.instantiate(
				0,
				&mut GasMeter::<Test>::with_limit(10000, 1),
				&rent_allowance_ch,
				vec![],
			);
			assert_matches!(result, Ok(_));
		});
	}
}
