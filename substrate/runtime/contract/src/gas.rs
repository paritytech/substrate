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

use {Trait, Module};
use runtime_primitives::traits::{As, CheckedMul, CheckedSub, Zero};
use staking;

#[must_use]
#[derive(Debug, PartialEq, Eq)]
pub enum GasMeterResult {
	Proceed,
	OutOfGas,
}

impl GasMeterResult {
	pub fn is_out_of_gas(&self) -> bool {
		match *self {
			GasMeterResult::OutOfGas => true,
			GasMeterResult::Proceed => false,
		}
	}
}

pub struct GasMeter<T: Trait> {
	gas_left: T::Gas,
	gas_price: T::Balance,
}
impl<T: Trait> GasMeter<T> {
	#[cfg(test)]
	pub fn with_limit(gas_limit: T::Gas, gas_price: T::Balance) -> GasMeter<T> {
		GasMeter {
			gas_left: gas_limit,
			gas_price,
		}
	}

	/// Account for used gas.
	///
	/// Returns `OutOfGas` if there is not enough gas or addition of the specified
	/// amount of gas has lead to overflow. On success returns `Proceed`.
	///
	/// NOTE that `amount` is always consumed, i.e. if there is not enough gas
	/// then the counter will be set to zero.
	pub fn charge(&mut self, amount: T::Gas) -> GasMeterResult {
		let new_value = match self.gas_left.checked_sub(&amount) {
			None => None,
			Some(val) if val.is_zero() => None,
			Some(val) => Some(val),
		};

		// We always consume the gas even if there is not enough gas.
		self.gas_left = new_value.unwrap_or_else(Zero::zero);

		match new_value {
			Some(_) => GasMeterResult::Proceed,
			None => GasMeterResult::OutOfGas,
		}
	}

	/// Account for used gas expressed in balance units.
	///
	/// Same as [`charge`], but amount to be charged is converted from units of balance to
	/// units of gas.
	///
	/// [`charge`]: #method.charge
	pub fn charge_by_balance(&mut self, amount: T::Balance) -> GasMeterResult {
		let amount_in_gas: T::Balance = amount / self.gas_price;
		let amount_in_gas: T::Gas = <T::Gas as As<T::Balance>>::sa(amount_in_gas);
		self.charge(amount_in_gas)
	}

	/// Allocate some amount of gas and perform some work with
	/// a newly created nested gas meter.
	///
	/// Invokes `f` with either the gas meter that has `amount` gas left or
	/// with `None`, if this gas meter has not enough gas to allocate given `amount`.
	///
	/// All unused gas in the nested gas meter is returned to this gas meter.
	pub fn with_nested<R, F: FnOnce(Option<&mut GasMeter<T>>) -> R>(
		&mut self,
		amount: T::Gas,
		f: F,
	) -> R {
		// NOTE that it is ok to allocate all available gas since it still ensured
		// by `charge` that it doesn't reach zero.
		if self.gas_left < amount {
			f(None)
		} else {
			self.gas_left = self.gas_left - amount;
			let mut nested = GasMeter {
				gas_left: amount,
				gas_price: self.gas_price,
			};

			let r = f(Some(&mut nested));

			self.gas_left = self.gas_left + nested.gas_left;

			r
		}
	}

	/// Returns how much gas left from the initial budget.
	pub fn gas_left(&self) -> T::Gas {
		self.gas_left
	}
}

/// Buy the given amount of gas.
///
/// Cost is calculated by multiplying the gas cost (taken from the storage) by the `gas_limit`.
/// The funds are deducted from `transactor`.
pub fn buy_gas<T: Trait>(
	transactor: &T::AccountId,
	gas_limit: T::Gas,
) -> Result<GasMeter<T>, &'static str> {
	let gas_price = <Module<T>>::gas_price();
	let b = <staking::Module<T>>::free_balance(transactor);
	let cost = <T::Gas as As<T::Balance>>::as_(gas_limit.clone())
		.checked_mul(&gas_price)
		.ok_or("overflow multiplying gas limit by price")?;
	if b < cost + <staking::Module<T>>::existential_deposit() {
		return Err("not enough funds for transaction fee");
	}
	<staking::Module<T>>::set_free_balance(transactor, b - cost);
	<staking::Module<T>>::decrease_total_stake_by(cost);
	Ok(GasMeter {
		gas_left: gas_limit,
		gas_price,
	})
}

/// Refund the unused gas.
pub fn refund_unused_gas<T: Trait>(transactor: &T::AccountId, gas_meter: GasMeter<T>) {
	let b = <staking::Module<T>>::free_balance(transactor);
	let refund = <T::Gas as As<T::Balance>>::as_(gas_meter.gas_left) * gas_meter.gas_price;
	<staking::Module<T>>::set_free_balance(transactor, b + refund);
	<staking::Module<T>>::increase_total_stake_by(refund);
}
