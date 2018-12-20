// Copyright 2018 Parity Technologies (UK) Ltd.
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

use super::{CodeHash, Config, ContractAddressFor, Event, RawEvent, Schedule, Trait};
use account_db::{AccountDb, OverlayAccountDb};
use code;
use gas::GasMeter;

use balances::{self, EnsureAccountLiquid};
use rstd::prelude::*;
use runtime_primitives::traits::{CheckedAdd, CheckedSub, Zero};

pub type BalanceOf<T> = <T as balances::Trait>::Balance;
pub type AccountIdOf<T> = <T as system::Trait>::AccountId;

// TODO: Add logs
pub struct CreateReceipt<T: Trait> {
	pub address: T::AccountId,
}

// TODO: Add logs.
#[cfg_attr(test, derive(Debug))]
pub struct CallReceipt;

/// An interface that provides an access to the external environment in which the
/// smart-contract is executed.
///
/// This interface is specialised to an account of the executing code, so all
/// operations are implicitly performed on that account.
pub trait Ext {
	type T: Trait;

	/// Returns the storage entry of the executing account by the given key.
	fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Sets the storage entry by the given key to the specified value.
	fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>);

	/// Create a new account for a contract.
	///
	/// The newly created account will be associated with the `code`. `value` specifies the amount of value
	/// transfered from this to the newly created account.
	fn create(
		&mut self,
		code: &CodeHash<Self::T>,
		value: BalanceOf<Self::T>,
		gas_meter: &mut GasMeter<Self::T>,
		data: &[u8],
	) -> Result<CreateReceipt<Self::T>, &'static str>;

	/// Call (possibly transfering some amount of funds) into the specified account.
	fn call(
		&mut self,
		to: &AccountIdOf<Self::T>,
		value: BalanceOf<Self::T>,
		gas_meter: &mut GasMeter<Self::T>,
		data: &[u8],
		output_data: &mut Vec<u8>,
	) -> Result<(), &'static str>;

	/// Returns a reference to the account id of the caller.
	fn caller(&self) -> &AccountIdOf<Self::T>;
}

pub trait Loader<T: Trait> {
	type Executable;

	fn load_init(&self, code_hash: &CodeHash<T>) -> Result<Self::Executable, &'static str>;
	fn load_main(&self, code_hash: &CodeHash<T>) -> Result<Self::Executable, &'static str>;
}

pub trait Vm<T: Trait> {
	type Executable;

	fn execute<E: Ext<T = T>>(
		&self,
		exec: &Self::Executable,
		ext: &mut E,
		input_data: &[u8],
		output_data: &mut Vec<u8>,
		gas_meter: &mut GasMeter<T>,
	) -> Result<(), &'static str>;
}

pub struct WasmExecutable {
	// TODO: Remove these pubs
	pub entrypoint_name: &'static [u8],
	pub memory_def: ::code::MemoryDefinition,
	pub instrumented_code: Vec<u8>,
}

pub struct WasmLoader<'a, T: Trait> {
	schedule: &'a Schedule<T::Gas>,
}

impl<'a, T: Trait> WasmLoader<'a, T> {
	pub fn new(schedule: &'a Schedule<T::Gas>) -> Self {
		WasmLoader { schedule }
	}
}

impl<'a, T: Trait> Loader<T> for WasmLoader<'a, T> {
	type Executable = WasmExecutable;

	fn load_init(&self, code_hash: &CodeHash<T>) -> Result<WasmExecutable, &'static str> {
		let dest_code = code::load::<T>(code_hash, self.schedule)?;
		Ok(WasmExecutable {
			entrypoint_name: b"deploy",
			memory_def: dest_code.memory_def,
			instrumented_code: dest_code.code,
		})
	}
	fn load_main(&self, code_hash: &CodeHash<T>) -> Result<WasmExecutable, &'static str> {
		let dest_code = code::load::<T>(code_hash, self.schedule)?;
		Ok(WasmExecutable {
			entrypoint_name: b"call",
			memory_def: dest_code.memory_def,
			instrumented_code: dest_code.code,
		})
	}
}

pub struct ExecutionContext<'a, T: Trait + 'a, V, L> {
	// typically should be dest
	pub self_account: T::AccountId,
	pub overlay: OverlayAccountDb<'a, T>,
	pub depth: usize,
	pub events: Vec<Event<T>>,
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
	/// Make a call to the specified address.
	pub fn call(
		&mut self,
		caller: T::AccountId,
		dest: T::AccountId,
		value: T::Balance,
		gas_meter: &mut GasMeter<T>,
		input_data: &[u8],
		output_data: &mut Vec<u8>,
	) -> Result<CallReceipt, &'static str> {
		if self.depth == self.config.max_depth as usize {
			return Err("reached maximum depth, cannot make a call");
		}

		if gas_meter.charge(self.config.call_base_fee).is_out_of_gas() {
			return Err("not enough gas to pay base call fee");
		}

		let dest_code_hash = self.overlay.get_code(&dest);

		let (change_set, events) = {
			let mut overlay = OverlayAccountDb::new(&self.overlay);

			let mut nested = ExecutionContext {
				overlay: overlay,
				self_account: dest.clone(),
				depth: self.depth + 1,
				events: Vec::new(),
				config: self.config,
				vm: self.vm,
				loader: self.loader,
			};

			if value > T::Balance::zero() {
				transfer(
					gas_meter,
					false,
					&self.self_account,
					&dest,
					value,
					&mut nested,
				)?;
			}

			if let Some(dest_code_hash) = dest_code_hash {
				let executable = self.loader.load_main(&dest_code_hash)?;
				self.vm.execute(
					&executable,
					&mut CallContext {
						ctx: &mut nested,
						caller: caller,
					},
					input_data,
					output_data,
					gas_meter,
				)?;
			}

			(nested.overlay.into_change_set(), nested.events)
		};

		self.overlay.commit(change_set);
		self.events.extend(events);

		Ok(CallReceipt)
	}

	// TODO: rename it to instantiate.
	pub fn create(
		&mut self,
		caller: T::AccountId,
		endowment: T::Balance,
		gas_meter: &mut GasMeter<T>,
		code_hash: &CodeHash<T>,
		input_data: &[u8],
	) -> Result<CreateReceipt<T>, &'static str> {
		if self.depth == self.config.max_depth as usize {
			return Err("reached maximum depth, cannot create");
		}

		if gas_meter
			.charge(self.config.create_base_fee)
			.is_out_of_gas()
		{
			return Err("not enough gas to pay base create fee");
		}

		let dest = T::DetermineContractAddress::contract_address_for(
			code_hash,
			input_data,
			&self.self_account,
		);

		if self.overlay.get_code(&dest).is_some() {
			// It should be enough to check only the code.
			return Err("contract already exists");
		}

		let (change_set, events) = {
			let mut overlay = OverlayAccountDb::new(&self.overlay);
			overlay.set_code(&dest, Some(code_hash.clone()));

			let mut nested = ExecutionContext {
				overlay: overlay,
				self_account: dest.clone(),
				depth: self.depth + 1,
				events: Vec::new(),
				config: self.config,
				vm: self.vm,
				loader: self.loader,
			};

			if endowment > T::Balance::zero() {
				transfer(
					gas_meter,
					true,
					&self.self_account,
					&dest,
					endowment,
					&mut nested,
				)?;
			}

			// TODO: Do something with the output data.
			let mut output_data = Vec::<u8>::new();

			let executable = self.loader.load_init(&code_hash)?;
			self.vm.execute(
				&executable,
				&mut CallContext {
					ctx: &mut nested,
					caller: caller,
				},
				input_data,
				&mut output_data,
				gas_meter,
			)?;

			(nested.overlay.into_change_set(), nested.events)
		};

		self.overlay.commit(change_set);
		self.events.extend(events);

		Ok(CreateReceipt { address: dest })
	}
}

/// Transfer some funds from `transactor` to `dest`.
///
/// All balance changes are performed in the `overlay`.
///
/// This function also handles charging the fee. The fee depends
/// on whether the transfer happening because of contract creation
/// (transfering endowment), specified by `contract_create` flag,
/// or because of a transfer via `call`.
///
/// NOTE: that the fee is denominated in `T::Balance` units, but
/// charged in `T::Gas` from the provided `gas_meter`. This means
/// that the actual amount charged might differ.
///
/// NOTE: that we allow for draining all funds of the contract so it
/// can go below existential deposit, essentially giving a contract
/// the chance to give up it's life.
fn transfer<'a, T: Trait, V: Vm<T>, L: Loader<T>>(
	gas_meter: &mut GasMeter<T>,
	contract_create: bool,
	transactor: &T::AccountId,
	dest: &T::AccountId,
	value: T::Balance,
	ctx: &mut ExecutionContext<'a, T, V, L>,
) -> Result<(), &'static str> {
	let to_balance = ctx.overlay.get_balance(dest);

	// This flag is totally distinct from `contract_create`, which shows if this function
	// is called from `CREATE` procedure.
	//
	// `would_create` indicates whether the account will be created if this transfer gets executed.
	// For example, we can create a contract at the address which already has some funds. In this
	// case `contract_create` will be `true` but `would_create` will be `false`. Another example would
	// be when this function is called from `CALL`, but `dest` doesn't exist yet. In this case
	// `contract_create` will be `false` but `would_create` will be `true`.
	let would_create = to_balance.is_zero();

	let fee: T::Balance = match (contract_create, would_create) {
		// If this function is called from `CREATE` routine, then we always
		// charge contract account creation fee.
		(true, _) => ctx.config.contract_account_create_fee,

		// Otherwise the fee depends on whether we create a new account or transfer
		// to an existing one.
		(false, true) => ctx.config.account_create_fee,
		(false, false) => ctx.config.transfer_fee,
	};

	if gas_meter.charge_by_balance(fee).is_out_of_gas() {
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
	<T as balances::Trait>::EnsureAccountLiquid::ensure_account_liquid(transactor)?;

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
}

impl<'a, 'b: 'a, T, E, V, L> Ext for CallContext<'a, 'b, T, V, L>
where
	T: Trait + 'b,
	V: Vm<T, Executable = E>,
	L: Loader<T, Executable = E>,
{
	type T = T;

	fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.ctx.overlay.get_storage(&self.ctx.self_account, key)
	}

	fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>) {
		self.ctx
			.overlay
			.set_storage(&self.ctx.self_account, key.to_vec(), value)
	}

	fn create(
		&mut self,
		code_hash: &CodeHash<T>,
		endowment: T::Balance,
		gas_meter: &mut GasMeter<T>,
		data: &[u8],
	) -> Result<CreateReceipt<T>, &'static str> {
		let caller = self.ctx.self_account.clone();
		self.ctx
			.create(caller, endowment, gas_meter, code_hash, &data)
	}

	fn call(
		&mut self,
		to: &T::AccountId,
		value: T::Balance,
		gas_meter: &mut GasMeter<T>,
		data: &[u8],
		output_data: &mut Vec<u8>,
	) -> Result<(), &'static str> {
		let caller = self.ctx.self_account.clone();
		self.ctx
			.call(caller, to.clone(), value, gas_meter, data, output_data)
			.map(|_| ())
	}

	fn caller(&self) -> &T::AccountId {
		&self.caller
	}
}

#[cfg(test)]
mod tests {
	use super::{ExecutionContext, Ext, Loader, Vm};
	use account_db::{DirectAccountDb, OverlayAccountDb};
	use gas::GasMeter;
	use runtime_io::with_externalities;
	use std::cell::RefCell;
	use std::collections::HashMap;
	use std::marker::PhantomData;
	use std::rc::Rc;
	use tests::{ExtBuilder, Test};
	use {CodeHash, Config};

	const ALICE: u64 = 1;
	const BOB: u64 = 2;
	const CHARLIE: u64 = 3;

	struct MockCtx<'a> {
		ext: &'a mut dyn Ext<T = Test>,
		input_data: &'a [u8],
		output_data: &'a mut Vec<u8>,
		gas_meter: &'a mut GasMeter<Test>,
	}

	#[derive(Clone)]
	struct MockExecutable<'a>(Rc<Fn(MockCtx) -> Result<(), &'static str> + 'a>);

	impl<'a> MockExecutable<'a> {
		fn new(f: impl Fn(MockCtx) -> Result<(), &'static str> + 'a) -> Self {
			MockExecutable(Rc::new(f))
		}
	}

	struct MockLoader<'a> {
		map: HashMap<CodeHash<Test>, MockExecutable<'a>>,
	}
	struct MockVm<'a> {
		_data: PhantomData<&'a ()>,
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
			output_data: &mut Vec<u8>,
			gas_meter: &mut GasMeter<Test>,
		) -> Result<(), &'static str> {
			(exec.0)(MockCtx {
				ext,
				input_data,
				output_data,
				gas_meter,
			})
		}
	}

	#[test]
	fn it_works() {
		let origin = 0;
		let dest = 1;
		let value = Default::default();
		let mut gas_meter = GasMeter::<Test>::with_limit(10000, 1);
		let data = vec![];
		let mut output_data = Vec::new();

		let vm = MockVm { _data: PhantomData };

		let test_data = Rc::new(RefCell::new(vec![0usize]));

		{
			let loader = MockLoader {
				map: {
					let mut contracts = HashMap::new();
					contracts.insert(
						1.into(),
						MockExecutable::new(|_ctx| {
							test_data.borrow_mut().push(1);
							Ok(())
						}),
					);
					contracts
				},
			};

			with_externalities(&mut ExtBuilder::default().build(), || {
				let mut overlay = OverlayAccountDb::<Test>::new(&DirectAccountDb);
				overlay.set_code(&1, Some(1.into()));

				let cfg = Config::preload();

				let mut ctx = ExecutionContext {
					self_account: origin.clone(),
					depth: 0,
					overlay,
					events: Vec::new(),
					config: &cfg,
					vm: &vm,
					loader: &loader,
				};

				let result = ctx.call(
					origin.clone(),
					dest,
					value,
					&mut gas_meter,
					&data,
					&mut output_data,
				);

				assert_matches!(result, Ok(_));
			});
		}

		assert_eq!(&*test_data.borrow(), &vec![0, 1]);
	}

	#[test]
	fn input_data() {
		let origin = ALICE;
		let dest = BOB;
		let value = Default::default();

		let vm = MockVm { _data: PhantomData };

		let loader = MockLoader {
			map: {
				let mut contracts = HashMap::new();
				contracts.insert(
					1.into(),
					MockExecutable::new(|ctx| {
						assert_eq!(ctx.input_data, &[1, 2, 3, 4]);
						Ok(())
					}),
				);
				contracts
			},
		};

		with_externalities(&mut ExtBuilder::default().build(), || {
			let mut overlay = OverlayAccountDb::<Test>::new(&DirectAccountDb);
			overlay.set_code(&dest, Some(1.into()));

			let cfg = Config::preload();

			let mut ctx = ExecutionContext {
				self_account: origin.clone(),
				depth: 0,
				overlay,
				events: Vec::new(),
				config: &cfg,
				vm: &vm,
				loader: &loader,
			};

			let result = ctx.call(
				origin.clone(),
				dest,
				value,
				&mut GasMeter::<Test>::with_limit(10000, 1),
				&[1, 2, 3, 4],
				&mut vec![],
			);

			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn max_depth() {
		let origin = ALICE;
		let dest = BOB;
		let value = Default::default();

		let vm = MockVm { _data: PhantomData };

		let reached_bottom = RefCell::new(false);

		let loader = MockLoader {
			map: {
				let mut contracts = HashMap::new();
				contracts.insert(
					1.into(),
					MockExecutable::new(|ctx| {
						// Try to call into yourself.
						let r = ctx.ext.call(&BOB, 0, ctx.gas_meter, &[], &mut vec![]);

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

						Ok(())
					}),
				);
				contracts
			},
		};

		with_externalities(&mut ExtBuilder::default().build(), || {
			let mut overlay = OverlayAccountDb::<Test>::new(&DirectAccountDb);
			overlay.set_code(&dest, Some(1.into()));

			let cfg = Config::preload();

			let mut ctx = ExecutionContext {
				self_account: origin.clone(),
				depth: 0,
				overlay,
				events: Vec::new(),
				config: &cfg,
				vm: &vm,
				loader: &loader,
			};

			let result = ctx.call(
				origin.clone(),
				dest,
				value,
				&mut GasMeter::<Test>::with_limit(100000, 1),
				&[],
				&mut vec![],
			);

			assert_matches!(result, Ok(_));
		});
	}

	#[test]
	fn caller_returns_proper_values() {
		let origin = ALICE;
		let dest = BOB;
		let value = Default::default();

		let vm = MockVm { _data: PhantomData };

		let witnessed_caller_bob = RefCell::new(None::<u64>);
		let witnessed_caller_charlie = RefCell::new(None::<u64>);

		let loader = MockLoader {
			map: {
				let mut contracts = HashMap::new();
				contracts.insert(
					1.into(),
					MockExecutable::new(|ctx| {
						// Witness caller for bob.
						*witnessed_caller_bob.borrow_mut() = Some(*ctx.ext.caller());

						// Call into CHARLIE contract.
						let r = ctx.ext.call(&CHARLIE, 0, ctx.gas_meter, &[], &mut vec![]);
						assert_matches!(r, Ok(_));
						Ok(())
					}),
				);
				contracts.insert(
					2.into(),
					MockExecutable::new(|ctx| {
						// Witness caller for charlie.
						*witnessed_caller_charlie.borrow_mut() = Some(*ctx.ext.caller());
						Ok(())
					}),
				);
				contracts
			},
		};

		with_externalities(&mut ExtBuilder::default().build(), || {
			let mut overlay = OverlayAccountDb::<Test>::new(&DirectAccountDb);
			overlay.set_code(&dest, Some(1.into()));
			overlay.set_code(&CHARLIE, Some(2.into()));

			let cfg = Config::preload();

			let mut ctx = ExecutionContext {
				self_account: origin.clone(),
				depth: 0,
				overlay,
				events: Vec::new(),
				config: &cfg,
				vm: &vm,
				loader: &loader,
			};

			let result = ctx.call(
				origin.clone(),
				dest,
				value,
				&mut GasMeter::<Test>::with_limit(10000, 1),
				&[],
				&mut vec![],
			);

			assert_matches!(result, Ok(_));
		});

		assert_eq!(&*witnessed_caller_bob.borrow(), &Some(origin));
		assert_eq!(&*witnessed_caller_charlie.borrow(), &Some(dest));
	}
}
