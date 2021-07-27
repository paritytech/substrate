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

//! A module that implements instrumented code cache.
//!
//! - In order to run contract code we need to instrument it with gas metering.
//! To do that we need to provide the schedule which will supply exact gas costs values.
//! We cache this code in the storage saving the schedule version.
//! - Before running contract code we check if the cached code has the schedule version that
//! is equal to the current saved schedule.
//! If it is equal then run the code, if it isn't reinstrument with the current schedule.
//! - When we update the schedule we want it to have strictly greater version than the current saved one:
//! this guarantees that every instrumented contract code in cache cannot have the version equal to the current one.
//! Thus, before executing a contract it should be reinstrument with new schedule.

#[cfg(feature = "runtime-benchmarks")]
pub use self::private::reinstrument;
use crate::{
	gas::{GasMeter, Token},
	wasm::{prepare, PrefabWasmModule},
	weights::WeightInfo,
	CodeHash, CodeStorage, Config, Error, Event, Pallet as Contracts, PristineCode, Schedule,
	Weight,
};
use frame_support::dispatch::DispatchError;
use sp_core::crypto::UncheckedFrom;

/// Put the instrumented module in storage.
///
/// Increments the refcount of the in-storage `prefab_module` if it already exists in storage
/// under the specified `code_hash`.
pub fn store<T: Config>(mut prefab_module: PrefabWasmModule<T>)
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	let code_hash = sp_std::mem::take(&mut prefab_module.code_hash);

	// original_code is only `Some` if the contract was instantiated from a new code
	// but `None` if it was loaded from storage.
	if let Some(code) = prefab_module.original_code.take() {
		<PristineCode<T>>::insert(&code_hash, code);
	}
	<CodeStorage<T>>::mutate(&code_hash, |existing| match existing {
		Some(module) => increment_64(&mut module.refcount),
		None => {
			*existing = Some(prefab_module);
			Contracts::<T>::deposit_event(Event::CodeStored(code_hash))
		},
	});
}

/// Decrement the refcount and store.
///
/// Removes the code instead of storing it when the refcount drops to zero.
pub fn store_decremented<T: Config>(mut prefab_module: PrefabWasmModule<T>)
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	prefab_module.refcount = prefab_module.refcount.saturating_sub(1);
	if prefab_module.refcount > 0 {
		<CodeStorage<T>>::insert(prefab_module.code_hash, prefab_module);
	} else {
		<CodeStorage<T>>::remove(prefab_module.code_hash);
		finish_removal::<T>(prefab_module.code_hash);
	}
}

/// Increment the refcount of a code in-storage by one.
pub fn increment_refcount<T: Config>(
	code_hash: CodeHash<T>,
	gas_meter: &mut GasMeter<T>,
) -> Result<(), DispatchError>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	gas_meter.charge(CodeToken::UpdateRefcount(estimate_code_size::<T>(&code_hash)?))?;
	<CodeStorage<T>>::mutate(code_hash, |existing| {
		if let Some(module) = existing {
			increment_64(&mut module.refcount);
			Ok(())
		} else {
			Err(Error::<T>::CodeNotFound.into())
		}
	})
}

/// Decrement the refcount of a code in-storage by one and remove the code when it drops to zero.
pub fn decrement_refcount<T: Config>(
	code_hash: CodeHash<T>,
	gas_meter: &mut GasMeter<T>,
) -> Result<(), DispatchError>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	if let Ok(len) = estimate_code_size::<T>(&code_hash) {
		gas_meter.charge(CodeToken::UpdateRefcount(len))?;
	}
	<CodeStorage<T>>::mutate_exists(code_hash, |existing| {
		if let Some(module) = existing {
			module.refcount = module.refcount.saturating_sub(1);
			if module.refcount == 0 {
				*existing = None;
				finish_removal::<T>(code_hash);
			}
		}
	});
	Ok(())
}

/// Load code with the given code hash.
///
/// If the module was instrumented with a lower version of schedule than
/// the current one given as an argument, then this function will perform
/// re-instrumentation and update the cache in the storage.
///
/// # Note
///
/// If `reinstrument` is set it is assumed that the load is performed in the context of
/// a contract call: This means we charge the size based cased for loading the contract.
pub fn load<T: Config>(
	code_hash: CodeHash<T>,
	mut reinstrument: Option<(&Schedule<T>, &mut GasMeter<T>)>,
) -> Result<PrefabWasmModule<T>, DispatchError>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	// The reinstrument case coincides with the cases where we need to charge extra
	// based upon the code size: On-chain execution.
	if let Some((_, gas_meter)) = &mut reinstrument {
		gas_meter.charge(CodeToken::Load(estimate_code_size::<T>(&code_hash)?))?;
	}

	let mut prefab_module =
		<CodeStorage<T>>::get(code_hash).ok_or_else(|| Error::<T>::CodeNotFound)?;
	prefab_module.code_hash = code_hash;

	if let Some((schedule, gas_meter)) = reinstrument {
		if prefab_module.instruction_weights_version < schedule.instruction_weights.version {
			// The instruction weights have changed.
			// We need to re-instrument the code with the new instruction weights.
			gas_meter.charge(CodeToken::Instrument(prefab_module.original_code_len))?;
			private::reinstrument(&mut prefab_module, schedule)?;
		}
	}
	Ok(prefab_module)
}

mod private {
	use super::*;

	/// Instruments the passed prefab wasm module with the supplied schedule.
	pub fn reinstrument<T: Config>(
		prefab_module: &mut PrefabWasmModule<T>,
		schedule: &Schedule<T>,
	) -> Result<(), DispatchError>
	where
		T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
	{
		let original_code = <PristineCode<T>>::get(&prefab_module.code_hash)
			.ok_or_else(|| Error::<T>::CodeNotFound)?;
		prefab_module.code = prepare::reinstrument_contract::<T>(original_code, schedule)?;
		prefab_module.instruction_weights_version = schedule.instruction_weights.version;
		<CodeStorage<T>>::insert(&prefab_module.code_hash, &*prefab_module);
		Ok(())
	}
}

/// Finish removal of a code by deleting the pristine code and emitting an event.
fn finish_removal<T: Config>(code_hash: CodeHash<T>)
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	<PristineCode<T>>::remove(code_hash);
	Contracts::<T>::deposit_event(Event::CodeRemoved(code_hash))
}

/// Increment the refcount panicking if it should ever overflow (which will not happen).
///
/// We try hard to be infallible here because otherwise more storage transactions would be
/// necessary to account for failures in storing code for an already instantiated contract.
fn increment_64(refcount: &mut u64) {
	*refcount = refcount.checked_add(1).expect(
		"
		refcount is 64bit. Generating this overflow would require to store
		_at least_ 18 exabyte of data assuming that a contract consumes only
		one byte of data. Any node would run out of storage space before hitting
		this overflow.
		qed
	",
	);
}

/// Get the size of the instrumented code stored at `code_hash` without loading it.
///
/// The returned value is slightly too large because it also contains the fields apart from
/// `code` which are located inside [`PrefabWasmModule`]. However, those are negligible when
/// compared to the code size. Additionally, charging too much weight is completely safe.
fn estimate_code_size<T: Config>(code_hash: &CodeHash<T>) -> Result<u32, DispatchError>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	let key = <CodeStorage<T>>::hashed_key_for(code_hash);
	let mut data = [0u8; 0];
	let len = sp_io::storage::read(&key, &mut data, 0).ok_or_else(|| Error::<T>::CodeNotFound)?;
	Ok(len)
}

/// Costs for operations that are related to code handling.
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
enum CodeToken {
	/// Weight for instrumenting a contract contract of the supplied size in bytes.
	Instrument(u32),
	/// Weight for loading a contract per kilobyte.
	Load(u32),
	/// Weight for changing the refcount of a contract per kilobyte.
	UpdateRefcount(u32),
}

impl<T> Token<T> for CodeToken
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	fn weight(&self) -> Weight {
		use self::CodeToken::*;
		// In case of `Load` and `UpdateRefcount` we already covered the general costs of
		// accessing the storage but still need to account for the actual size of the
		// contract code. This is why we substract `T::*::(0)`. We need to do this at this
		// point because when charging the general weight we do not know the size of
		// the contract.
		match *self {
			Instrument(len) => T::WeightInfo::instrument(len / 1024),
			Load(len) =>
				T::WeightInfo::code_load(len / 1024).saturating_sub(T::WeightInfo::code_load(0)),
			UpdateRefcount(len) => T::WeightInfo::code_refcount(len / 1024)
				.saturating_sub(T::WeightInfo::code_refcount(0)),
		}
	}
}
