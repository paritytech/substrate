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

use crate::{
	CodeHash, CodeStorage, PristineCode, Schedule, Config, Error,
	wasm::{prepare, PrefabWasmModule}, Module as Contracts, RawEvent,
};
use sp_core::crypto::UncheckedFrom;
use frame_support::{StorageMap, dispatch::{DispatchError, DispatchResult}};

/// Put the instrumented module in storage.
///
/// Increments the refcount of the in-storage `prefab_module` if it already exists in storage
/// under the specified `code_hash`.
pub fn store<T: Config>(mut prefab_module: PrefabWasmModule<T>)
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>
{
	let code_hash = sp_std::mem::take(&mut prefab_module.code_hash);

	// original_code is only `Some` if the contract was instantiated from a new code
	// but `None` if it was loaded from storage.
	if let Some(code) = prefab_module.original_code.take() {
		<PristineCode<T>>::insert(&code_hash, code);
	}
	<CodeStorage<T>>::mutate(&code_hash, |existing| {
		match existing {
			Some(module) => increment_64(&mut module.refcount),
			None => {
				*existing = Some(prefab_module);
				Contracts::<T>::deposit_event(RawEvent::CodeStored(code_hash))
			}
		}
	});
}

/// Decrement the refcount and store.
///
/// Removes the code instead of storing it when the refcount drops to zero.
pub fn store_decremented<T: Config>(mut prefab_module: PrefabWasmModule<T>)
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>
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
pub fn increment_refcount<T: Config>(code_hash: CodeHash<T>) -> DispatchResult
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>
{
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
pub fn decrement_refcount<T: Config>(code_hash: CodeHash<T>)
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>
{
	<CodeStorage<T>>::mutate_exists(code_hash, |existing| {
		if let Some(module) = existing {
			module.refcount = module.refcount.saturating_sub(1);
			if module.refcount == 0 {
				*existing = None;
				finish_removal::<T>(code_hash);
			}
		}
	});
}

/// Load code with the given code hash.
///
/// If the module was instrumented with a lower version of schedule than
/// the current one given as an argument, then this function will perform
/// re-instrumentation and update the cache in the storage.
pub fn load<T: Config>(
	code_hash: CodeHash<T>,
	schedule: Option<&Schedule<T>>,
) -> Result<PrefabWasmModule<T>, DispatchError>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>
{
	let mut prefab_module = <CodeStorage<T>>::get(code_hash)
		.ok_or_else(|| Error::<T>::CodeNotFound)?;

	if let Some(schedule) = schedule {
		if prefab_module.schedule_version < schedule.version {
			// The current schedule version is greater than the version of the one cached
			// in the storage.
			//
			// We need to re-instrument the code with the latest schedule here.
			let original_code = <PristineCode<T>>::get(code_hash)
				.ok_or_else(|| Error::<T>::CodeNotFound)?;
			prefab_module.code = prepare::reinstrument_contract::<T>(original_code, schedule)?;
			prefab_module.schedule_version = schedule.version;
			<CodeStorage<T>>::insert(&code_hash, &prefab_module);
		}
	}
	prefab_module.code_hash = code_hash;
	Ok(prefab_module)
}

/// Finish removal of a code by deleting the pristine code and emitting an event.
fn finish_removal<T: Config>(code_hash: CodeHash<T>)
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>
{
	<PristineCode<T>>::remove(code_hash);
	Contracts::<T>::deposit_event(RawEvent::CodeRemoved(code_hash))
}

/// Increment the refcount panicking if it should ever overflow (which will not happen).
///
/// We try hard to be infallible here because otherwise more storage transactions would be
/// necessary to account for failures in storing code for an already instantiated contract.
fn increment_64(refcount: &mut u64) {
	*refcount = refcount.checked_add(1).expect("
		refcount is 64bit. Generating this overflow would require to store
		_at least_ 18 exabyte of data assuming that a contract consumes only
		one byte of data. Any node would run out of storage space before hitting
		this overflow.
		qed
	");
}
