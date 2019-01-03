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

use codec::Compact;
use gas::{GasMeter, Token};
use rstd::prelude::*;
use runtime_primitives::traits::{As, CheckedMul, Hash};
use runtime_support::StorageMap;
use wasm::{
	PrefabWasmModule,
	prepare,
	runtime::Env,
};
use {CodeHash, CodeStorage, PrestineCode, Schedule, Trait};

/// Gas metering token that used for charging storing code into the code storage.
///
/// Specifies the code length in bytes.
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub struct PutCodeToken(u64);

impl<T: Trait> Token<T> for PutCodeToken {
	type Metadata = Schedule<T::Gas>;

	fn calculate_amount(&self, metadata: &Schedule<T::Gas>) -> Option<T::Gas> {
		let code_len_in_gas = <T::Gas as As<u64>>::sa(self.0);
		let cost = metadata
			.put_code_per_byte_cost
			.checked_mul(&code_len_in_gas)?;

		Some(cost)
	}
}

pub fn save<T: Trait>(
	original_code: Vec<u8>,
	gas_meter: &mut GasMeter<T>,
	schedule: &Schedule<T::Gas>,
) -> Result<CodeHash<T>, &'static str> {
	// The first time instrumentation is on the user. However, consequent reinstrumentation
	// due to the schedule changes is on governance system.
	if gas_meter
		.charge(
			schedule,
			PutCodeToken(original_code.len() as u64)
		)
		.is_out_of_gas()
	{
		return Err("there is not enough gas for storing the code");
	}

	let instrumented_module = prepare::prepare_contract::<T, Env>(&original_code, schedule)?;
	let code_hash = T::Hashing::hash(&original_code);

	// TODO: validate the code. If the code is not valid, then don't store it.

	<CodeStorage<T>>::insert(code_hash, instrumented_module);
	<PrestineCode<T>>::insert(code_hash, original_code);

	Ok(code_hash)
}

pub fn load<T: Trait>(
	code_hash: &CodeHash<T>,
	schedule: &Schedule<T::Gas>,
) -> Result<PrefabWasmModule, &'static str> {
	let instrumented_module =
		<CodeStorage<T>>::get(code_hash).ok_or_else(|| "code is not found")?;

	if instrumented_module.schedule_version < schedule.version {
		let original_code =
			<PrestineCode<T>>::get(code_hash).ok_or_else(|| "prestine code is not found")?;

		let instrumented_module = prepare::prepare_contract::<T, Env>(&original_code, schedule)?;

		<CodeStorage<T>>::insert(code_hash, instrumented_module.clone());

		Ok(instrumented_module)
	} else {
		Ok(instrumented_module)
	}
}
