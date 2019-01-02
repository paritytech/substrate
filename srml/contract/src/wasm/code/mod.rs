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
use gas::GasMeter;
use rstd::prelude::*;
use runtime_primitives::traits::{As, CheckedMul, Hash};
use runtime_support::StorageMap;
use wasm::runtime::Env;
use {CodeHash, CodeStorage, PrestineCode, Schedule, Trait};

pub mod prepare;

#[derive(Clone, Encode, Decode)]
pub struct MemoryDefinition {
	#[codec(compact)]
	pub initial: u32,
	#[codec(compact)]
	pub maximum: u32,
}

#[derive(Clone, Encode, Decode)]
pub struct InstrumentedWasmModule {
	/// Version of the schedule with which the code was instrumented.
	#[codec(compact)]
	schedule_version: u32,
	pub memory_def: MemoryDefinition,
	/// Code instrumented with the latest schedule.
	pub code: Vec<u8>,
}

pub fn save<T: Trait>(
	original_code: Vec<u8>,
	gas_meter: &mut GasMeter<T>,
	schedule: &Schedule<T::Gas>,
) -> Result<CodeHash<T>, &'static str> {
	let code_len_in_gas = <T::Gas as As<u64>>::sa(original_code.len() as u64);
	let cost = schedule
		.put_code_per_byte_cost
		.checked_mul(&code_len_in_gas)
		.ok_or_else(|| "overflow occured when calculating put_code price")?;
	if gas_meter.charge(cost).is_out_of_gas() {
		return Err("there is not enough gas");
	}

	let code_hash = T::Hashing::hash(&original_code);

	// The first time instrumentation is on the user. However, consequent reinstrumentation
	// due to the schedule changes is on governance system.
	let instrumented_module = prepare::prepare_contract::<T, Env>(&original_code, schedule)?;

	// TODO: validate the code. If the code is not valid, then don't store it.

	<CodeStorage<T>>::insert(code_hash, instrumented_module);
	<PrestineCode<T>>::insert(code_hash, original_code);

	Ok(code_hash)
}

pub fn load<T: Trait>(
	code_hash: &CodeHash<T>,
	schedule: &Schedule<T::Gas>,
) -> Result<InstrumentedWasmModule, &'static str> {
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
