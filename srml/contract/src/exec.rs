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
	TrieId, BalanceOf, ContractInfoOf};
use crate::account_db::{AccountDb, DirectAccountDb, OverlayAccountDb};
use crate::gas::{GasMeter, Token, approx_gas_for_balance};

use rstd::prelude::*;
use runtime_primitives::traits::{Bounded, CheckedAdd, CheckedSub, Zero};
use srml_support::{StorageMap, traits::{WithdrawReason, Currency}};
use timestamp;

pub type AccountIdOf<T> = <T as system::Trait>::AccountId;
pub type CallOf<T> = <T as Trait>::Call;
pub type MomentOf<T> = <T as timestamp::Trait>::Moment;
pub type SeedOf<T> = <T as system::Trait>::Hash;

#[cfg_attr(test, derive(Debug))]
pub struct InstantiateReceipt<AccountId> {
	pub address: AccountId,
}

#[cfg_attr(test, derive(Debug))]
pub struct CallReceipt {
	/// Output data received as a result of a call.
	pub output_data: Vec<u8>,
}

pub type StorageKey = [u8; 32];

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

	/// Sets the storage entry by the given key to the specified value.
	///
	/// If `value` is `None` then the storage entry is deleted.
	fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>);

	/// Instantiate a contract from the given code.
	///
	/// The newly created account will be associated with `code`. `value` specifies the amount of value
	/// transfered from this to the newly created account (also known as endowment).
	fn instantiate(
		&mut self,
		code: &CodeHash<Self::T>,
		value: BalanceOf<Self::T>,
		gas_meter: &mut GasMeter<Self::T>,
		input_data: &[u8],
	) -> Result<InstantiateReceipt<AccountIdOf<Self::T>>, &'static str>;

	/// Call (possibly transfering some amount of funds) into the specified account.
	fn call(
		&mut self,
		to: &AccountIdOf<Self::T>,
		value: BalanceOf<Self::T>,
		gas_meter: &mut GasMeter<Self::T>,
		input_data: &[u8],
		empty_output_buf: EmptyOutputBuf,
	) -> Result<CallReceipt, &'static str>;

	/// Notes a call dispatch.
	fn note_dispatch_call(&mut self, call: CallOf<Self::T>);

	/// Returns a reference to the account id of the caller.
	fn caller(&self) -> &AccountIdOf<Self::T>;

	/// Returns a reference to the account id of the current contract.
	fn address(&self) -> &AccountIdOf<Self::T>;

	/// Returns the balance of the current contract.
	///
	/// The `value_transferred` is already added.
	fn balance(&self) -> BalanceOf<Self::T>;

	/// Returns the value transfered along with this call or as endowment.
	fn value_transferred(&self) -> BalanceOf<Self::T>;

	/// Returns a reference to the timestamp of the current block
	fn now(&self) -> &MomentOf<Self::T>;

	/// Returns a reference to the random seed for the current block
	fn random_seed(&self) -> &SeedOf<Self::T>;

	/// Deposit an event.
	fn deposit_event(&mut self, data: Vec<u8>);

	/// Set rent allowance of the contract
	fn set_rent_allowance(&mut self, rent_allowance: BalanceOf<Self::T>);

	/// Rent allowance of the contract
	fn rent_allowance(&self) -> BalanceOf<Self::T>;
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

/// An `EmptyOutputBuf` is used as an optimization for reusing empty vectors when
/// available.
///
/// You can create this structure from a spare vector if you have any and then
/// you can fill it (only once), converting it to `OutputBuf`.
pub struct EmptyOutputBuf(Vec<u8>);

impl EmptyOutputBuf {
	/// Create an output buffer from a spare vector which is not longer needed.
	///
	/// All contents are discarded, but capacity is preserved.
	pub fn from_spare_vec(mut v: Vec<u8>) -> Self {
		v.clear();
		EmptyOutputBuf(v)
	}

	/// Create an output buffer ready for receiving a result.
	///
	/// Use this function to create output buffer if you don't have a spare
	/// vector. Otherwise, use `from_spare_vec`.
	pub fn new() -> Self {
		EmptyOutputBuf(Vec::new())
	}

	/// Write to the buffer result of the specified size.
	///
	/// Calls closure with the buffer of the requested size.
	pub fn fill<E, F: FnOnce(&mut [u8]) -> Result<(), E>>(mut self, size: usize, f: F) -> Result<OutputBuf, E> {
		assert!(self.0.len() == 0, "the vector is always cleared; it's written only once");
		self.0.resize(size, 0);
		f(&mut self.0).map(|()| OutputBuf(self.0))
	}
}

/// `OutputBuf` is the end result of filling an `EmptyOutputBuf`.
pub struct OutputBuf(Vec<u8>);

#[must_use]
pub enum VmExecResult {
	Ok,
	Returned(OutputBuf),
	/// A program executed some forbidden operation.
	///
	/// This can include, e.g.: division by 0, OOB access or failure to satisfy some precondition
	/// of a system call.
	///
	/// Contains some vm-specific description of an trap.
	Trap(&'static str),
}

impl VmExecResult {
	pub fn into_result(self) -> Result<Vec<u8>, &'static str> {
		match self {
			VmExecResult::Ok => Ok(Vec::new()),
			VmExecResult::Returned(buf) => Ok(buf.0),
			VmExecResult::Trap(description) => Err(description),
		}
	}
}

/// A trait that represent a virtual machine.
///
/// You can view a virtual machine as something that takes code, an input data buffer,
/// queries it and/or performs actions on the given `Ext` and optionally
/// returns an output data buffer. The type of code depends on the particular virtual machine.
///
/// Execution of code can end by either implicit termination (that is, reached the end of
/// executable), explicit termination via returning a buffer or termination due to a trap.
///
/// You can optionally provide a vector for collecting output if a spare is available. If you don't have
/// it will be created anyway.
pub trait Vm<T: Trait> {
	type Executable;

	fn execute<E: Ext<T = T>>(
		&self,
		exec: &Self::Executable,
		ext: &mut E,
		input_data: &[u8],
		empty_output_buf: EmptyOutputBuf,
		gas_meter: &mut GasMeter<T>,
	) -> VmExecResult;
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
	fn calculate_amount(&self, metadata: &Config<T>) -> T::Gas {
		match *self {
			ExecFeeToken::Call => metadata.call_base_fee,
			ExecFeeToken::Instantiate => metadata.instantiate_base_fee,
		}
	}
}

pub struct ExecutionContext<'a, T: Trait + 'a, V, L> {
	pub self_account: T::AccountId,
	pub self_trie_id: Option<TrieId>,
	pub overlay: OverlayAccountDb<'a, T>,
	pub depth: usize,
	pub events: Vec<Event<T>>,
	pub calls: Vec<(T::AccountId, T::Call)>,
	pub config: &'a Config<T>,
	pub vm: &'a V,
	pub loader: &'a L,
}

impl<'a, T, E, V, L> ExecutionContext<'a, T, V, L>
where
	T: Trait,
	L: Loader<T, Executable = E>,
	V: Vm<T, Executable = E>,
{
	/// Create the top level execution context.
	///
	/// The specified `origin` address will be used as `sender` for
	pub fn top_level(origin: T::AccountId, cfg: &'a Config<T>, vm: &'a V, loader: &'a L) -> Self {
		ExecutionContext {
			self_trie_id: <ContractInfoOf<T>>::get(&origin)
				.and_then(|i| i.as_alive().map(|i| i.trie_id.clone())),
			self_account: origin,
			overlay: OverlayAccountDb::<T>::new(&DirectAccountDb),
			depth: 0,
			events: Vec::new(),
			calls: Vec::new(),
			config: &cfg,
			vm: &vm,
			loader: &loader,
		}
	}

	fn nested(&self, overlay: OverlayAccountDb<'a, T>, dest: T::AccountId) -> Self {
		ExecutionContext {
			self_trie_id: <ContractInfoOf<T>>::get(&dest)
				.and_then(|i| i.as_alive().map(|i| i.trie_id.clone())),
			self_account: dest,
			overlay,
			depth: self.depth + 1,
			events: Vec::new(),
			calls: Vec::new(),
			config: self.config,
			vm: self.vm,
			loader: self.loader,
		}
	}

	/// Make a call to the specified address, optionally transfering some funds.
	pub fn call(
		&mut self,
		dest: T::AccountId,
		value: BalanceOf<T>,
		gas_meter: &mut GasMeter<T>,
		input_data: &[u8],
		empty_output_buf: EmptyOutputBuf,
	) -> Result<CallReceipt, &'static str> {
		if self.depth == self.config.max_depth as usize {
			return Err("reached maximum depth, cannot make a call");
		}

		if gas_meter
			.charge(self.config, ExecFeeToken::Call)
			.is_out_of_gas()
		{
			return Err("not enough gas to pay base call fee");
		}

		// Assumption: pay_rent doesn't collide with overlay because
		// pay_rent will be done on first call and dest contract and balance
		// cannot be changed before the first call
		crate::rent::pay_rent::<T>(&dest);

		let mut output_data = Vec::new();

		let (change_set, events, calls) = {
			let mut nested = self.nested(
				OverlayAccountDb::new(&self.overlay),
				dest.clone()
			);

			if value > BalanceOf::<T>::zero() {
				transfer(
					gas_meter,
					TransferCause::Call,
					&self.self_account,
					&dest,
					value,
					&mut nested,
				)?;
			}

			if let Some(dest_code_hash) = self.overlay.get_code_hash(&dest) {
				let executable = self.loader.load_main(&dest_code_hash)?;
				output_data = self
					.vm
					.execute(
						&executable,
						&mut CallContext {
							ctx: &mut nested,
							caller: self.self_account.clone(),
							value_transferred: value,
							timestamp: timestamp::Module::<T>::now(),
							random_seed: system::Module::<T>::random_seed(),
						},
						input_data,
						empty_output_buf,
						gas_meter,
					)
					.into_result()?;
			}

			(nested.overlay.into_change_set(), nested.events, nested.calls)
		};

		self.overlay.commit(change_set);
		self.events.extend(events);
		self.calls.extend(calls);

		Ok(CallReceipt { output_data })
	}

	pub fn instantiate(
		&mut self,
		endowment: BalanceOf<T>,
		gas_meter: &mut GasMeter<T>,
		code_hash: &CodeHash<T>,
		input_data: &[u8],
	) -> Result<InstantiateReceipt<T::AccountId>, &'static str> {
		if self.depth == self.config.max_depth as usize {
			return Err("reached maximum depth, cannot create");
		}

		if gas_meter
			.charge(self.config, ExecFeeToken::Instantiate)
			.is_out_of_gas()
		{
			return Err("not enough gas to pay base instantiate fee");
		}

		let dest = T::DetermineContractAddress::contract_address_for(
			code_hash,
			input_data,
			&self.self_account,
		);

		let (change_set, events, calls) = {
			let mut overlay = OverlayAccountDb::new(&self.overlay);

			overlay.create_contract(&dest, code_hash.clone())?;

			let mut nested = self.nested(overlay, dest.clone());

			// Send funds unconditionally here. If the `endowment` is below existential_deposit
			// then error will be returned here.
			transfer(
				gas_meter,
				TransferCause::Instantiate,
				&self.self_account,
				&dest,
				endowment,
				&mut nested,
			)?;

			let executable = self.loader.load_init(&code_hash)?;
			self.vm
				.execute(
					&executable,
					&mut CallContext {
						ctx: &mut nested,
						caller: self.self_account.clone(),
						value_transferred: endowment,
						timestamp: timestamp::Module::<T>::now(),
						random_seed: system::Module::<T>::random_seed(),
					},
					input_data,
					EmptyOutputBuf::new(),
					gas_meter,
				)
				.into_result()?;

			// Deposit an instantiation event.
			nested.events.push(RawEvent::Instantiated(self.self_account.clone(), dest.clone()));

			(nested.overlay.into_change_set(), nested.events, nested.calls)
		};

		self.overlay.commit(change_set);
		self.events.extend(events);
		self.calls.extend(calls);

		Ok(InstantiateReceipt { address: dest })
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
	fn calculate_amount(&self, metadata: &Config<T>) -> T::Gas {
		let balance_fee = match self.kind {
			TransferFeeKind::ContractInstantiate => metadata.contract_account_instantiate_fee,
			TransferFeeKind::AccountCreate => metadata.account_create_fee,
			TransferFeeKind::Transfer => metadata.transfer_fee,
		};
		approx_gas_for_balance::<T>(self.gas_price, balance_fee)
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
/// (transfering endowment) or because of a transfer via `call`. This
/// is specified using the `cause` parameter.
///
/// NOTE: that the fee is denominated in `BalanceOf<T>` units, but
/// charged in `T::Gas` from the provided `gas_meter`. This means
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
	T::Currency::ensure_can_withdraw(transactor, value, WithdrawReason::Transfer, new_from_balance)?;

	let new_to_balance = match to_balance.checked_add(&value) {
		Some(b) => b,
		None => return Err("destination balance too high to receive value"),
	};

	if transactor != dest {
		ctx.overlay.set_balance(transactor, new_from_balance);
		ctx.overlay.set_balance(dest, new_to_balance);
		ctx.events
			.push(RawEvent::Transfer(transactor.clone(), dest.clone(), value));
	}

	Ok(())
}

struct CallContext<'a, 'b: 'a, T: Trait + 'b, V: Vm<T> + 'b, L: Loader<T>> {
	ctx: &'a mut ExecutionContext<'b, T, V, L>,
	caller: T::AccountId,
	value_transferred: BalanceOf<T>,
	timestamp: T::Moment,
	random_seed: T::Hash,
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

	fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>) {
		self.ctx
			.overlay
			.set_storage(&self.ctx.self_account, key, value)
	}

	fn instantiate(
		&mut self,
		code_hash: &CodeHash<T>,
		endowment: BalanceOf<T>,
		gas_meter: &mut GasMeter<T>,
		input_data: &[u8],
	) -> Result<InstantiateReceipt<AccountIdOf<T>>, &'static str> {
		self.ctx.instantiate(endowment, gas_meter, code_hash, input_data)
	}

	fn call(
		&mut self,
		to: &T::AccountId,
		value: BalanceOf<T>,
		gas_meter: &mut GasMeter<T>,
		input_data: &[u8],
		empty_output_buf: EmptyOutputBuf,
	) -> Result<CallReceipt, &'static str> {
		self.ctx
			.call(to.clone(), value, gas_meter, input_data, empty_output_buf)
	}

	/// Notes a call dispatch.
	fn note_dispatch_call(&mut self, call: CallOf<Self::T>) {
		self.ctx.calls.push(
			(self.ctx.self_account.clone(), call)
		);
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

	fn random_seed(&self) -> &T::Hash {
		&self.random_seed
	}

	fn now(&self) -> &T::Moment {
		&self.timestamp
	}

	fn deposit_event(&mut self, data: Vec<u8>) {
		self.ctx.events.push(RawEvent::Contract(self.ctx.self_account.clone(), data));
	}

	fn set_rent_allowance(&mut self, rent_allowance: BalanceOf<T>) {
		self.ctx.overlay.set_rent_allowance(&self.ctx.self_account, rent_allowance)
	}

	fn rent_allowance(&self) -> BalanceOf<T> {
		self.ctx.overlay.get_rent_allowance(&self.ctx.self_account)
			.unwrap_or(<BalanceOf<T>>::max_value()) // Must never be triggered actually
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
		BalanceOf, ExecFeeToken, ExecutionContext, Ext, Loader, EmptyOutputBuf, TransferFeeKind, TransferFeeToken,
		Vm, VmExecResult, InstantiateReceipt, RawEvent,
	};
	use crate::account_db::AccountDb;
	use crate::gas::GasMeter;
	use crate::tests::{ExtBuilder, Test};
	use crate::{CodeHash, Config};
	use runtime_io::with_externalities;
	use std::cell::RefCell;
	use std::rc::Rc;
	use std::collections::HashMap;
	use std::marker::PhantomData;
	use assert_matches::assert_matches;

	const ALICE: u64 = 1;
	const BOB: u64 = 2;
	const CHARLIE: u64 = 3;

	struct MockCtx<'a> {
		ext: &'a mut dyn Ext<T = Test>,
		input_data: &'a [u8],
		empty_output_buf: Option<EmptyOutputBuf>,
		gas_meter: &'a mut GasMeter<Test>,
	}

	#[derive(Clone)]
	struct MockExecutable<'a>(Rc<Fn(MockCtx) -> VmExecResult + 'a>);

	impl<'a> MockExecutable<'a> {
		fn new(f: impl Fn(MockCtx) -> VmExecResult + 'a) -> Self {
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

		fn insert(&mut self, f: impl Fn(MockCtx) -> VmExecResult + 'a) -> CodeHash<Test> {
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
			ext: &mut E,
			input_data: &[u8],
			empty_output_buf: EmptyOutputBuf,
			gas_meter: &mut GasMeter<Test>,
		) -> VmExecResult {
			(exec.0)(MockCtx {
				ext,
				input_data,
				empty_output_buf: Some(empty_output_buf),
				gas_meter,
			})
		}
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
			VmExecResult::Ok
		});

		with_externalities(&mut ExtBuilder::default().build(), || {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			ctx.overlay.create_contract(&BOB, exec_ch).unwrap();

			assert_matches!(
				ctx.call(BOB, value, &mut gas_meter, &data, EmptyOutputBuf::new()),
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
		with_externalities(&mut ExtBuilder::default().build(), || {
			let vm = MockVm::new();
			let loader = MockLoader::empty();
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			ctx.overlay.set_balance(&origin, 100);
			ctx.overlay.set_balance(&dest, 0);

			let mut gas_meter = GasMeter::<Test>::with_limit(1000, 1);

			let result = ctx.call(dest, 0, &mut gas_meter, &[], EmptyOutputBuf::new());
			assert_matches!(result, Ok(_));

			let mut toks = gas_meter.tokens().iter();
			match_tokens!(toks, ExecFeeToken::Call,);
		});

		// This test verifies that base fee for instantiation is taken.
		with_externalities(&mut ExtBuilder::default().build(), || {
			let mut loader = MockLoader::empty();
			let code = loader.insert(|_| VmExecResult::Ok);

			let vm = MockVm::new();
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);

			ctx.overlay.set_balance(&origin, 100);

			let mut gas_meter = GasMeter::<Test>::with_limit(1000, 1);

			let result = ctx.instantiate(0, &mut gas_meter, &code, &[]);
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

		with_externalities(&mut ExtBuilder::default().build(), || {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			ctx.overlay.set_balance(&origin, 100);
			ctx.overlay.set_balance(&dest, 0);

			let result = ctx.call(
				dest,
				55,
				&mut GasMeter::<Test>::with_limit(1000, 1),
				&[],
				EmptyOutputBuf::new(),
			);
			assert_matches!(result, Ok(_));
			assert_eq!(ctx.overlay.get_balance(&origin), 45);
			assert_eq!(ctx.overlay.get_balance(&dest), 55);
		});
	}

	#[test]
	fn transfer_fees() {
		let origin = ALICE;
		let dest = BOB;

		// This test sends 50 units of currency to a non-existent account.
		// This should create lead to creation of a new account thus
		// a fee should be charged.
		with_externalities(
			&mut ExtBuilder::default().existential_deposit(15).build(),
			|| {
				let vm = MockVm::new();
				let loader = MockLoader::empty();
				let cfg = Config::preload();
				let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
				ctx.overlay.set_balance(&origin, 100);
				ctx.overlay.set_balance(&dest, 0);

				let mut gas_meter = GasMeter::<Test>::with_limit(1000, 1);

				let result = ctx.call(dest, 50, &mut gas_meter, &[], EmptyOutputBuf::new());
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
			},
		);

		// This one is similar to the previous one but transfer to an existing account.
		// In this test we expect that a regular transfer fee is charged.
		with_externalities(
			&mut ExtBuilder::default().existential_deposit(15).build(),
			|| {
				let vm = MockVm::new();
				let loader = MockLoader::empty();
				let cfg = Config::preload();
				let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
				ctx.overlay.set_balance(&origin, 100);
				ctx.overlay.set_balance(&dest, 15);

				let mut gas_meter = GasMeter::<Test>::with_limit(1000, 1);

				let result = ctx.call(dest, 50, &mut gas_meter, &[], EmptyOutputBuf::new());
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
			},
		);

		// This test sends 50 units of currency as an endownment to a newly
		// created contract.
		with_externalities(
			&mut ExtBuilder::default().existential_deposit(15).build(),
			|| {
				let mut loader = MockLoader::empty();
				let code = loader.insert(|_| VmExecResult::Ok);

				let vm = MockVm::new();
				let cfg = Config::preload();
				let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);

				ctx.overlay.set_balance(&origin, 100);
				ctx.overlay.set_balance(&dest, 15);

				let mut gas_meter = GasMeter::<Test>::with_limit(1000, 1);

				let result = ctx.instantiate(50, &mut gas_meter, &code, &[]);
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
			},
		);
	}

	#[test]
	fn balance_too_low() {
		// This test verifies that a contract can't send value if it's
		// balance is too low.
		let origin = ALICE;
		let dest = BOB;

		let vm = MockVm::new();
		let loader = MockLoader::empty();

		with_externalities(&mut ExtBuilder::default().build(), || {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			ctx.overlay.set_balance(&origin, 0);

			let result = ctx.call(
				dest,
				100,
				&mut GasMeter::<Test>::with_limit(1000, 1),
				&[],
				EmptyOutputBuf::new(),
			);

			assert_matches!(result, Err("balance too low to send value"));
			assert_eq!(ctx.overlay.get_balance(&origin), 0);
			assert_eq!(ctx.overlay.get_balance(&dest), 0);
		});
	}

	#[test]
	fn output_is_returned() {
		// Verifies that if a contract returns data, this data
		// is returned from the execution context.
		let origin = ALICE;
		let dest = BOB;

		let vm = MockVm::new();
		let mut loader = MockLoader::empty();
		let return_ch = loader.insert(|mut ctx| {
			#[derive(Debug)]
			enum Void {}
			let empty_output_buf = ctx.empty_output_buf.take().unwrap();
			let output_buf =
				empty_output_buf.fill::<Void, _>(4, |data| {
					data.copy_from_slice(&[1, 2, 3, 4]);
					Ok(())
				})
				.expect("Ok is always returned");
			VmExecResult::Returned(output_buf)
		});

		with_externalities(&mut ExtBuilder::default().build(), || {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			ctx.overlay.create_contract(&BOB, return_ch).unwrap();

			let result = ctx.call(
				dest,
				0,
				&mut GasMeter::<Test>::with_limit(1000, 1),
				&[],
				EmptyOutputBuf::new(),
			);

			let output_data = result.unwrap().output_data;
			assert_eq!(&output_data, &[1, 2, 3, 4]);
		});
	}

	#[test]
	fn input_data() {
		let vm = MockVm::new();
		let mut loader = MockLoader::empty();
		let input_data_ch = loader.insert(|ctx| {
			assert_eq!(ctx.input_data, &[1, 2, 3, 4]);
			VmExecResult::Ok
		});

		// This one tests passing the input data into a contract via call.
		with_externalities(&mut ExtBuilder::default().build(), || {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			ctx.overlay.create_contract(&BOB, input_data_ch).unwrap();

			let result = ctx.call(
				BOB,
				0,
				&mut GasMeter::<Test>::with_limit(10000, 1),
				&[1, 2, 3, 4],
				EmptyOutputBuf::new(),
			);
			assert_matches!(result, Ok(_));
		});

		// This one tests passing the input data into a contract via instantiate.
		with_externalities(&mut ExtBuilder::default().build(), || {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);

			let result = ctx.instantiate(
				0,
				&mut GasMeter::<Test>::with_limit(10000, 1),
				&input_data_ch,
				&[1, 2, 3, 4],
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
			let r = ctx
				.ext
				.call(&BOB, 0, ctx.gas_meter, &[], EmptyOutputBuf::new());

			let mut reached_bottom = reached_bottom.borrow_mut();
			if !*reached_bottom {
				// We are first time here, it means we just reached bottom.
				// Verify that we've got proper error and set `reached_bottom`.
				assert_matches!(r, Err("reached maximum depth, cannot make a call"));
				*reached_bottom = true;
			} else {
				// We just unwinding stack here.
				assert_matches!(r, Ok(_));
			}

			VmExecResult::Ok
		});

		with_externalities(&mut ExtBuilder::default().build(), || {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			ctx.overlay.create_contract(&BOB, recurse_ch).unwrap();

			let result = ctx.call(
				BOB,
				value,
				&mut GasMeter::<Test>::with_limit(100000, 1),
				&[],
				EmptyOutputBuf::new(),
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
				ctx.ext
					.call(&CHARLIE, 0, ctx.gas_meter, &[], EmptyOutputBuf::new()),
				Ok(_)
			);
			VmExecResult::Ok
		});
		let charlie_ch = loader.insert(|ctx| {
			// Record the caller for charlie.
			*witnessed_caller_charlie.borrow_mut() = Some(*ctx.ext.caller());
			VmExecResult::Ok
		});

		with_externalities(&mut ExtBuilder::default().build(), || {
			let cfg = Config::preload();

			let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
			ctx.overlay.create_contract(&dest, bob_ch).unwrap();
			ctx.overlay.create_contract(&CHARLIE, charlie_ch).unwrap();

			let result = ctx.call(
				dest,
				0,
				&mut GasMeter::<Test>::with_limit(10000, 1),
				&[],
				EmptyOutputBuf::new(),
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
				ctx.ext
					.call(&CHARLIE, 0, ctx.gas_meter, &[], EmptyOutputBuf::new()),
				Ok(_)
			);
			VmExecResult::Ok
		});
		let charlie_ch = loader.insert(|ctx| {
			assert_eq!(*ctx.ext.address(), CHARLIE);
			VmExecResult::Ok
		});

		with_externalities(&mut ExtBuilder::default().build(), || {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
			ctx.overlay.create_contract(&BOB, bob_ch).unwrap();
			ctx.overlay.create_contract(&CHARLIE, charlie_ch).unwrap();

			let result = ctx.call(
				BOB,
				0,
				&mut GasMeter::<Test>::with_limit(10000, 1),
				&[],
				EmptyOutputBuf::new(),
			);

			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn refuse_instantiate_with_value_below_existential_deposit() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let dummy_ch = loader.insert(|_| VmExecResult::Ok);

		with_externalities(
			&mut ExtBuilder::default().existential_deposit(15).build(),
			|| {
				let cfg = Config::preload();
				let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);

				assert_matches!(
					ctx.instantiate(
						0, // <- zero endowment
						&mut GasMeter::<Test>::with_limit(10000, 1),
						&dummy_ch,
						&[],
					),
					Err(_)
				);
			}
		);
	}

	#[test]
	fn instantiation() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let dummy_ch = loader.insert(|_| VmExecResult::Ok);

		with_externalities(
			&mut ExtBuilder::default().existential_deposit(15).build(),
			|| {
				let cfg = Config::preload();
				let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
				ctx.overlay.set_balance(&ALICE, 1000);

				let created_contract_address = assert_matches!(
					ctx.instantiate(
						100,
						&mut GasMeter::<Test>::with_limit(10000, 1),
						&dummy_ch,
						&[],
					),
					Ok(InstantiateReceipt { address }) => address
				);

				// Check that the newly created account has the expected code hash and
				// there are instantiation event.
				assert_eq!(ctx.overlay.get_code_hash(&created_contract_address).unwrap(), dummy_ch);
				assert_eq!(&ctx.events, &[
					RawEvent::Transfer(ALICE, created_contract_address, 100),
					RawEvent::Instantiated(ALICE, created_contract_address),
				]);
			}
		);
	}

	#[test]
	fn instantiation_from_contract() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let dummy_ch = loader.insert(|_| VmExecResult::Ok);
		let created_contract_address = Rc::new(RefCell::new(None::<u64>));
		let creator_ch = loader.insert({
			let dummy_ch = dummy_ch.clone();
			let created_contract_address = Rc::clone(&created_contract_address);
			move |ctx| {
				// Instantiate a contract and save it's address in `created_contract_address`.
				*created_contract_address.borrow_mut() =
					ctx.ext.instantiate(
						&dummy_ch,
						15u64,
						ctx.gas_meter,
						&[]
					)
					.unwrap()
					.address.into();

				VmExecResult::Ok
			}
		});

		with_externalities(
			&mut ExtBuilder::default().existential_deposit(15).build(),
			|| {
				let cfg = Config::preload();
				let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
				ctx.overlay.set_balance(&ALICE, 1000);
				ctx.overlay.create_contract(&BOB, creator_ch).unwrap();

				assert_matches!(
					ctx.call(BOB, 20, &mut GasMeter::<Test>::with_limit(1000, 1), &[], EmptyOutputBuf::new()),
					Ok(_)
				);

				let created_contract_address = created_contract_address.borrow().as_ref().unwrap().clone();

				// Check that the newly created account has the expected code hash and
				// there are instantiation event.
				assert_eq!(ctx.overlay.get_code_hash(&created_contract_address).unwrap(), dummy_ch);
				assert_eq!(&ctx.events, &[
					RawEvent::Transfer(ALICE, BOB, 20),
					RawEvent::Transfer(BOB, created_contract_address, 15),
					RawEvent::Instantiated(BOB, created_contract_address),
				]);
			}
		);
	}

	#[test]
	fn instantiation_fails() {
		let vm = MockVm::new();

		let mut loader = MockLoader::empty();
		let dummy_ch = loader.insert(|_| VmExecResult::Trap("It's a trap!"));
		let creator_ch = loader.insert({
			let dummy_ch = dummy_ch.clone();
			move |ctx| {
				// Instantiate a contract and save it's address in `created_contract_address`.
				assert_matches!(
					ctx.ext.instantiate(
						&dummy_ch,
						15u64,
						ctx.gas_meter,
						&[]
					),
					Err("It's a trap!")
				);

				VmExecResult::Ok
			}
		});

		with_externalities(
			&mut ExtBuilder::default().existential_deposit(15).build(),
			|| {
				let cfg = Config::preload();
				let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);
				ctx.overlay.set_balance(&ALICE, 1000);
				ctx.overlay.create_contract(&BOB, creator_ch).unwrap();

				assert_matches!(
					ctx.call(BOB, 20, &mut GasMeter::<Test>::with_limit(1000, 1), &[], EmptyOutputBuf::new()),
					Ok(_)
				);

				// The contract wasn't created so we don't expect to see an instantiation
				// event here.
				assert_eq!(&ctx.events, &[
					RawEvent::Transfer(ALICE, BOB, 20),
				]);
			}
		);
	}

	#[test]
	fn rent_allowance() {
		let vm = MockVm::new();
		let mut loader = MockLoader::empty();
		let rent_allowance_ch = loader.insert(|ctx| {
			assert_eq!(ctx.ext.rent_allowance(), <BalanceOf<Test>>::max_value());
			ctx.ext.set_rent_allowance(10);
			assert_eq!(ctx.ext.rent_allowance(), 10);
			VmExecResult::Ok
		});

		with_externalities(&mut ExtBuilder::default().build(), || {
			let cfg = Config::preload();
			let mut ctx = ExecutionContext::top_level(ALICE, &cfg, &vm, &loader);

			let result = ctx.instantiate(
				0,
				&mut GasMeter::<Test>::with_limit(10000, 1),
				&rent_allowance_ch,
				&[],
			);
			assert_matches!(result, Ok(_));
		});
	}
}
