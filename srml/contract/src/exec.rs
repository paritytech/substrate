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

use super::{ContractAddressFor, Trait, Event, RawEvent, Config};
use account_db::{AccountDb, OverlayAccountDb};
use gas::GasMeter;
use vm;

use rstd::prelude::*;
use runtime_primitives::traits::{Zero, CheckedAdd, CheckedSub};
use balances::{self, EnsureAccountLiquid};

// TODO: Add logs
pub struct CreateReceipt<T: Trait> {
	pub address: T::AccountId,
}

// TODO: Add logs.
pub struct CallReceipt;

pub struct ExecutionContext<'a, T: Trait + 'a> {
	// typically should be dest
	pub self_account: T::AccountId,
	pub overlay: OverlayAccountDb<'a, T>,
	pub depth: usize,
	pub events: Vec<Event<T>>,
	pub config: &'a Config<T>,
}

impl<'a, T: Trait> ExecutionContext<'a, T> {
	/// Make a call to the specified address.
	pub fn call(
		&mut self,
		caller: T::AccountId,
		dest: T::AccountId,
		value: T::Balance,
		gas_meter: &mut GasMeter<T>,
		data: &[u8],
		output_data: &mut Vec<u8>,
	) -> Result<CallReceipt, &'static str> {
		if self.depth == self.config.max_depth as usize {
			return Err("reached maximum depth, cannot make a call");
		}

		if gas_meter.charge(self.config.call_base_fee).is_out_of_gas() {
			return Err("not enough gas to pay base call fee");
		}

		let dest_code = self.overlay.get_code(&dest);

		let (change_set, events) = {
			let mut overlay = OverlayAccountDb::new(&self.overlay);

			let mut nested = ExecutionContext {
				overlay: overlay,
				self_account: dest.clone(),
				depth: self.depth + 1,
				events: Vec::new(),
				config: self.config,
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

			if !dest_code.is_empty() {
				vm::execute(
					&dest_code,
					data,
					output_data,
					&mut CallContext {
						ctx: &mut nested,
						caller: caller,
					},
					&self.config.schedule,
					gas_meter,
				).map_err(|_| "vm execute returned error while call")?;
			}

			(nested.overlay.into_change_set(), nested.events)
		};

		self.overlay.commit(change_set);
		self.events.extend(events);

		Ok(CallReceipt)
	}

	pub fn create(
		&mut self,
		caller: T::AccountId,
		endowment: T::Balance,
		gas_meter: &mut GasMeter<T>,
		init_code: &[u8],
		data: &[u8],
	) -> Result<CreateReceipt<T>, &'static str> {
		if self.depth == self.config.max_depth as usize {
			return Err("reached maximum depth, cannot create");
		}

		if gas_meter.charge(self.config.create_base_fee).is_out_of_gas() {
			return Err("not enough gas to pay base create fee");
		}

		let dest = T::DetermineContractAddress::contract_address_for(init_code, data, &self.self_account);

		if !self.overlay.get_code(&dest).is_empty() {
			// It should be enough to check only the code.
			return Err("contract already exists");
		}

		let (change_set, events) = {
			let mut overlay = OverlayAccountDb::new(&self.overlay);

			let mut nested = ExecutionContext {
				overlay: overlay,
				self_account: dest.clone(),
				depth: self.depth + 1,
				events: Vec::new(),
				config: self.config,
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

			let mut contract_code = Vec::new();
			vm::execute(
				init_code,
				data,
				&mut contract_code,
				&mut CallContext {
					ctx: &mut nested,
					caller: caller,
				},
				&self.config.schedule,
				gas_meter,
			).map_err(|_| "vm execute returned error while create")?;

			nested.overlay.set_code(&dest, contract_code);
			(nested.overlay.into_change_set(), nested.events)
		};

		self.overlay.commit(change_set);
		self.events.extend(events);

		Ok(CreateReceipt {
			address: dest,
		})
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
fn transfer<'a, T: Trait>(
	gas_meter: &mut GasMeter<T>,
	contract_create: bool,
	transactor: &T::AccountId,
	dest: &T::AccountId,
	value: T::Balance,
	ctx: &mut ExecutionContext<'a, T>,
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
		ctx.events.push(RawEvent::Transfer(transactor.clone(), dest.clone(), value));
	}

	Ok(())
}

struct CallContext<'a, 'b: 'a, T: Trait + 'b> {
	ctx: &'a mut ExecutionContext<'b, T>,
	caller: T::AccountId,
}

impl<'a, 'b: 'a, T: Trait + 'b> vm::Ext for CallContext<'a, 'b, T> {
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
		code: &[u8],
		endowment: T::Balance,
		gas_meter: &mut GasMeter<T>,
		data: &[u8],
	) -> Result<CreateReceipt<T>, ()> {
		let caller = self.ctx.self_account.clone();
		self.ctx
			.create(caller, endowment, gas_meter, code, &data)
			.map_err(|_| ())
	}

	fn call(
		&mut self,
		to: &T::AccountId,
		value: T::Balance,
		gas_meter: &mut GasMeter<T>,
		data: &[u8],
		output_data: &mut Vec<u8>,
	) -> Result<(), ()> {
		let caller = self.ctx.self_account.clone();
		self.ctx
			.call(caller, to.clone(), value, gas_meter, data, output_data)
			.map_err(|_| ())
			.map(|_| ())
	}

	fn caller(&self) -> &T::AccountId {
		&self.caller
	}
}
