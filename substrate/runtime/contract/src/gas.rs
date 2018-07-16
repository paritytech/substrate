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

use {Trait};
use staking;
use runtime_primitives::traits::As;

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

pub struct GasMeter {
	gas_left: u64,
}
impl GasMeter {
	#[cfg(test)]
	pub fn with_limit(gas_limit: u64) -> GasMeter {
		GasMeter {
			gas_left: gas_limit,
		}
	}

	/// Account for used gas.
	///
	/// Returns `OutOfGas` if there is not enough gas or addition of the specified
	/// amount of gas has lead to overflow. On success returns `Proceed`.
	pub fn charge(&mut self, amount: u64) -> GasMeterResult {
		match self.gas_left.checked_sub(amount) {
			None => GasMeterResult::OutOfGas,
			Some(val) if val == 0 => GasMeterResult::OutOfGas,
			Some(val) => {
				self.gas_left = val;
				GasMeterResult::Proceed
			}
		}
	}

	pub fn with_nested<R, F: FnOnce(Option<&mut GasMeter>) -> R>(&mut self, amount: u64, f: F) -> R {
		// NOTE that it is ok to allocate all available gas since it still ensured
		// by `charge` that it doesn't reach zero.
		if self.gas_left < amount {
			f(None)
		} else {
			self.gas_left -= amount;
			let mut nested = GasMeter {
				gas_left: amount,
			};

			let r = f(Some(&mut nested));

			self.gas_left += nested.gas_left;

			r
		}
	}

	/// Returns how much gas left from the initial budget.
	pub fn gas_left(&self) -> u64 {
		self.gas_left
	}
}

pub fn pay_for_gas<T: Trait>(transactor: &T::AccountId, gas_limit: u64, gas_price: u64) -> Result<GasMeter, &'static str> {
	let b = <staking::Module<T>>::free_balance(transactor);
	let cost = gas_limit
		.checked_mul(gas_price)
		.ok_or("overflow multiplying gas limit by price")?;
	let cost = <T::Balance as As<u64>>::sa(cost);
	if b < cost + <staking::Module<T>>::existential_deposit() {
		return Err("not enough funds for transaction fee");
	}
	<staking::Module<T>>::set_free_balance(transactor, b - cost);
	Ok(GasMeter {
		gas_left: gas_limit,
	})
}

pub fn refund_unused_gas<T: Trait>(transactor: &T::AccountId, gas_meter: GasMeter, gas_price: u64) {
	let b = <staking::Module<T>>::free_balance(transactor);
	let refund = gas_meter.gas_left * gas_price;
	let refund = <T::Balance as As<u64>>::sa(refund);
	<staking::Module<T>>::set_free_balance(transactor, b + refund);
}
