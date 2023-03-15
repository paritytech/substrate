// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
//! - When we update the schedule we want it to have strictly greater version than the current saved
//!   one:
//! this guarantees that every instrumented contract code in cache cannot have the version equal to
//! the current one. Thus, before executing a contract it should be reinstrument with new schedule.

use crate::{
	gas::{GasMeter, Token},
	wasm::{prepare, PrefabWasmModule},
	weights::WeightInfo,
	CodeHash, CodeStorage, Config, Error, Event, OwnerInfoOf, Pallet, PristineCode, Schedule,
	Weight,
};
use frame_support::{
	dispatch::{DispatchError, DispatchResult},
	ensure,
	traits::{Get, ReservableCurrency},
	WeakBoundedVec,
};
use sp_runtime::traits::BadOrigin;
use sp_std::vec;

/// Put the instrumented module in storage.
///
/// Increments the refcount of the in-storage `prefab_module` if it already exists in storage
/// under the specified `code_hash`.
pub fn store<T: Config>(mut module: PrefabWasmModule<T>, instantiated: bool) -> DispatchResult {
	let code_hash = sp_std::mem::take(&mut module.code_hash);
	<OwnerInfoOf<T>>::mutate(&code_hash, |owner_info| {
		match owner_info {
			// Instantiate existing contract.
			//
			// No need to update the `CodeStorage` as any re-instrumentation eagerly saves
			// the re-instrumented code.
			Some(owner_info) if instantiated => {
				owner_info.refcount = owner_info.refcount.checked_add(1).expect(
					"
					refcount is 64bit. Generating this overflow would require to store
					_at least_ 18 exabyte of data assuming that a contract consumes only
					one byte of data. Any node would run out of storage space before hitting
					this overflow.
					qed
				",
				);
				Ok(())
			},
			// Re-upload existing contract without executing it.
			//
			// We are careful here to just overwrite the code to not include it into the PoV.
			// We do this because the uploaded code was instrumented with the latest schedule
			// and hence we persist those changes. Otherwise the next execution will pay again
			// for the instrumentation.
			Some(_) => {
				<CodeStorage<T>>::insert(&code_hash, module);
				Ok(())
			},
			// Upload a new contract.
			//
			// We need to write all data structures and collect the deposit.
			None => {
				let orig_code = module.original_code.take().expect(
					"
					If an executable isn't in storage it was uploaded.
					If it was uploaded the original code must exist. qed
				",
				);
				let mut new_owner_info = module.owner_info.take().expect(
					"If an executable isn't in storage it was uploaded.
				If it was uploaded the owner info was generated and attached. qed
				",
				);
				// This `None` case happens only in freshly uploaded modules. This means that
				// the `owner` is always the origin of the current transaction.
				T::Currency::reserve(&new_owner_info.owner, new_owner_info.deposit)
					.map_err(|_| <Error<T>>::StorageDepositNotEnoughFunds)?;
				new_owner_info.refcount = if instantiated { 1 } else { 0 };
				<PristineCode<T>>::insert(&code_hash, orig_code);
				<CodeStorage<T>>::insert(&code_hash, module);
				*owner_info = Some(new_owner_info);
				<Pallet<T>>::deposit_event(vec![code_hash], Event::CodeStored { code_hash });
				Ok(())
			},
		}
	})
}

/// Decrement the refcount of a code in-storage by one.
///
/// # Note
///
/// A contract whose refcount dropped to zero isn't automatically removed. A `remove_code`
/// transaction must be submitted by the original uploader to do so.
pub fn decrement_refcount<T: Config>(code_hash: CodeHash<T>) {
	<OwnerInfoOf<T>>::mutate(code_hash, |existing| {
		if let Some(info) = existing {
			info.refcount = info.refcount.saturating_sub(1);
		}
	});
}

/// Increment the refcount of a code in-storage by one.
///
/// # Errors
///
/// [`Error::CodeNotFound`] is returned if the specified `code_hash` does not exist.
pub fn increment_refcount<T: Config>(code_hash: CodeHash<T>) -> Result<(), DispatchError> {
	<OwnerInfoOf<T>>::mutate(code_hash, |existing| -> Result<(), DispatchError> {
		if let Some(info) = existing {
			info.refcount = info.refcount.saturating_add(1);
			Ok(())
		} else {
			Err(Error::<T>::CodeNotFound.into())
		}
	})
}

/// Try to remove code together with all associated information.
pub fn try_remove<T: Config>(origin: &T::AccountId, code_hash: CodeHash<T>) -> DispatchResult {
	<OwnerInfoOf<T>>::try_mutate_exists(&code_hash, |existing| {
		if let Some(owner_info) = existing {
			ensure!(owner_info.refcount == 0, <Error<T>>::CodeInUse);
			ensure!(&owner_info.owner == origin, BadOrigin);
			T::Currency::unreserve(&owner_info.owner, owner_info.deposit);
			*existing = None;
			<PristineCode<T>>::remove(&code_hash);
			<CodeStorage<T>>::remove(&code_hash);
			<Pallet<T>>::deposit_event(vec![code_hash], Event::CodeRemoved { code_hash });
			Ok(())
		} else {
			Err(<Error<T>>::CodeNotFound.into())
		}
	})
}

/// Load code with the given code hash.
///
/// If the module was instrumented with a lower version of schedule than
/// the current one given as an argument, then this function will perform
/// re-instrumentation and update the cache in the storage.
pub fn load<T: Config>(
	code_hash: CodeHash<T>,
	schedule: &Schedule<T>,
	gas_meter: &mut GasMeter<T>,
) -> Result<PrefabWasmModule<T>, DispatchError> {
	let max_code_len = T::MaxCodeLen::get();
	let charged = gas_meter.charge(CodeToken::Load(max_code_len))?;

	let mut prefab_module = <CodeStorage<T>>::get(code_hash).ok_or(Error::<T>::CodeNotFound)?;
	let instrumented_code_len = prefab_module.code.len() as u32;
	gas_meter.adjust_gas(charged, CodeToken::Load(instrumented_code_len));
	prefab_module.code_hash = code_hash;

	if prefab_module.instruction_weights_version < schedule.instruction_weights.version {
		// The instruction weights have changed.
		// We need to re-instrument the code with the new instruction weights.
		let charged = gas_meter.charge(CodeToken::Reinstrument(instrumented_code_len))?;
		let orig_code_len = reinstrument(&mut prefab_module, schedule)?;
		gas_meter.adjust_gas(charged, CodeToken::Reinstrument(orig_code_len));
	}

	Ok(prefab_module)
}

/// Instruments the passed prefab wasm module with the supplied schedule.
///
/// Returns the size in bytes of the uninstrumented code.
pub fn reinstrument<T: Config>(
	prefab_module: &mut PrefabWasmModule<T>,
	schedule: &Schedule<T>,
) -> Result<u32, DispatchError> {
	let original_code =
		<PristineCode<T>>::get(&prefab_module.code_hash).ok_or(Error::<T>::CodeNotFound)?;
	let original_code_len = original_code.len();
	// We need to allow contracts growing too big after re-instrumentation. Otherwise
	// the contract can become inaccessible. The user has no influence over this size
	// as the contract is already deployed and every change in size would be the result
	// of changes in the instrumentation algorithm controlled by the chain authors.
	prefab_module.code = WeakBoundedVec::force_from(
		prepare::reinstrument::<super::runtime::Env, T>(
			&original_code,
			schedule,
			prefab_module.determinism,
		)?,
		Some("Contract exceeds size limit after re-instrumentation."),
	);
	prefab_module.instruction_weights_version = schedule.instruction_weights.version;
	<CodeStorage<T>>::insert(&prefab_module.code_hash, &*prefab_module);
	Ok(original_code_len as u32)
}

/// Costs for operations that are related to code handling.
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
enum CodeToken {
	/// Weight for reinstrumenting a contract contract of the supplied size in bytes.
	Reinstrument(u32),
	/// Weight for loading a contract per byte.
	Load(u32),
}

impl<T: Config> Token<T> for CodeToken {
	fn weight(&self) -> Weight {
		use self::CodeToken::*;
		// In case of `Load` we already covered the general costs of
		// calling the storage but still need to account for the actual size of the
		// contract code. This is why we subtract `T::*::(0)`. We need to do this at this
		// point because when charging the general weight for calling the contract we not know the
		// size of the contract.
		match *self {
			Reinstrument(len) => T::WeightInfo::reinstrument(len),
			Load(len) => T::WeightInfo::call_with_code_per_byte(len)
				.saturating_sub(T::WeightInfo::call_with_code_per_byte(0)),
		}
	}
}
