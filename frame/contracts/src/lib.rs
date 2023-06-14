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

//! # Contracts Pallet
//!
//! The Contracts module provides functionality for the runtime to deploy and execute WebAssembly
//! smart-contracts.
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! This module extends accounts based on the [`Currency`] trait to have smart-contract
//! functionality. It can be used with other modules that implement accounts based on [`Currency`].
//! These "smart-contract accounts" have the ability to instantiate smart-contracts and make calls
//! to other contract and non-contract accounts.
//!
//! The smart-contract code is stored once in a code cache, and later retrievable via its hash.
//! This means that multiple smart-contracts can be instantiated from the same hash, without
//! replicating the code each time.
//!
//! When a smart-contract is called, its associated code is retrieved via the code hash and gets
//! executed. This call can alter the storage entries of the smart-contract account, instantiate new
//! smart-contracts, or call other smart-contracts.
//!
//! Finally, when an account is reaped, its associated code and storage of the smart-contract
//! account will also be deleted.
//!
//! ### Gas
//!
//! Senders must specify a gas limit with every call, as all instructions invoked by the
//! smart-contract require gas. Unused gas is refunded after the call, regardless of the execution
//! outcome.
//!
//! If the gas limit is reached, then all calls and state changes (including balance transfers) are
//! only reverted at the current call's contract level. For example, if contract A calls B and B
//! runs out of gas mid-call, then all of B's calls are reverted. Assuming correct error handling by
//! contract A, A's other calls and state changes still persist.
//!
//! ### Notable Scenarios
//!
//! Contract call failures are not always cascading. When failures occur in a sub-call, they do not
//! "bubble up", and the call will only revert at the specific contract level. For example, if
//! contract A calls contract B, and B fails, A can decide how to handle that failure, either
//! proceeding or reverting A's changes.
//!
//! ## Interface
//!
//! ### Dispatchable functions
//!
//! * [`Pallet::instantiate_with_code`] - Deploys a new contract from the supplied wasm binary,
//! optionally transferring
//! some balance. This instantiates a new smart contract account with the supplied code and
//! calls its constructor to initialize the contract.
//! * [`Pallet::instantiate`] - The same as `instantiate_with_code` but instead of uploading new
//! code an existing `code_hash` is supplied.
//! * [`Pallet::call`] - Makes a call to an account, optionally transferring some balance.
//!
//! ## Usage
//!
//! The Contracts module is a work in progress. The following examples show how this module
//! can be used to instantiate and call contracts.
//!
//! * [`ink!`](https://use.ink) is
//! an [`eDSL`](https://wiki.haskell.org/Embedded_domain_specific_language) that enables writing
//! WebAssembly based smart contracts in the Rust programming language.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "runtime-benchmarks", recursion_limit = "1024")]

mod address;
mod benchmarking;
mod exec;
mod gas;
mod schedule;
mod storage;
mod wasm;

pub mod chain_extension;
pub mod migration;
pub mod weights;

#[cfg(test)]
mod tests;
use crate::{
	exec::{AccountIdOf, ErrorOrigin, ExecError, Executable, Key, Stack as ExecStack},
	gas::GasMeter,
	storage::{meter::Meter as StorageMeter, ContractInfo, DeletionQueueManager},
	wasm::{OwnerInfo, PrefabWasmModule, TryInstantiate},
};
use codec::{Codec, Decode, Encode, HasCompact};
use environmental::*;
use frame_support::{
	dispatch::{
		DispatchError, Dispatchable, GetDispatchInfo, Pays, PostDispatchInfo, RawOrigin,
		WithPostDispatchInfo,
	},
	ensure,
	error::BadOrigin,
	traits::{
		tokens::fungible::Inspect, ConstU32, Contains, Currency, Get, Randomness,
		ReservableCurrency, Time,
	},
	weights::Weight,
	BoundedVec, RuntimeDebugNoBound, WeakBoundedVec,
};
use frame_system::{ensure_signed, pallet_prelude::OriginFor, EventRecord, Pallet as System};
use pallet_contracts_primitives::{
	Code, CodeUploadResult, CodeUploadReturnValue, ContractAccessError, ContractExecResult,
	ContractInstantiateResult, ContractResult, ExecReturnValue, GetStorageResult,
	InstantiateReturnValue, StorageDeposit,
};
use scale_info::TypeInfo;
use smallvec::Array;
use sp_runtime::traits::{Convert, Hash, Saturating, StaticLookup, Zero};
use sp_std::{fmt::Debug, prelude::*};
pub use weights::WeightInfo;

pub use crate::{
	address::{AddressGenerator, DefaultAddressGenerator},
	exec::Frame,
	migration::{MigrateSequence, Migration, NoopMigration},
	pallet::*,
	schedule::{HostFnWeights, InstructionWeights, Limits, Schedule},
	wasm::Determinism,
};

#[cfg(doc)]
pub use crate::wasm::api_doc;

type CodeHash<T> = <T as frame_system::Config>::Hash;
type TrieId = BoundedVec<u8, ConstU32<128>>;
type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type CodeVec<T> = BoundedVec<u8, <T as Config>::MaxCodeLen>;
type RelaxedCodeVec<T> = WeakBoundedVec<u8, <T as Config>::MaxCodeLen>;
type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;
type DebugBufferVec<T> = BoundedVec<u8, <T as Config>::MaxDebugBufferLen>;
type EventRecordOf<T> =
	EventRecord<<T as frame_system::Config>::RuntimeEvent, <T as frame_system::Config>::Hash>;

/// The old weight type.
///
/// This is a copy of the [`frame_support::weights::OldWeight`] type since the contracts pallet
/// needs to support it indefinitely.
type OldWeight = u64;

/// Used as a sentinel value when reading and writing contract memory.
///
/// It is usually used to signal `None` to a contract when only a primitive is allowed
/// and we don't want to go through encoding a full Rust type. Using `u32::Max` is a safe
/// sentinel because contracts are never allowed to use such a large amount of resources
/// that this value makes sense for a memory location or length.
const SENTINEL: u32 = u32::MAX;

/// The target that is used for the log output emitted by this crate.
///
/// Hence you can use this target to selectively increase the log level for this crate.
///
/// Example: `RUST_LOG=runtime::contracts=debug my_code --dev`
const LOG_TARGET: &str = "runtime::contracts";

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	/// The current storage version.
	#[cfg(not(any(test, feature = "runtime-benchmarks")))]
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(11);

	/// Hard coded storage version for running tests that depend on the current storage version.
	#[cfg(any(test, feature = "runtime-benchmarks"))]
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(2);

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The time implementation used to supply timestamps to contracts through `seal_now`.
		type Time: Time;

		/// The generator used to supply randomness to contracts through `seal_random`.
		///
		/// # Deprecated
		///
		/// Codes using the randomness functionality cannot be uploaded. Neither can contracts
		/// be instantiated from existing codes that use this deprecated functionality. It will
		/// be removed eventually. Hence for new `pallet-contracts` deployments it is okay
		/// to supply a dummy implementation for this type (because it is never used).
		type Randomness: Randomness<Self::Hash, Self::BlockNumber>;

		/// The currency in which fees are paid and contract balances are held.
		type Currency: ReservableCurrency<Self::AccountId> // TODO: Move to fungible traits
			+ Inspect<Self::AccountId, Balance = BalanceOf<Self>>;

		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The overarching call type.
		type RuntimeCall: Dispatchable<RuntimeOrigin = Self::RuntimeOrigin, PostInfo = PostDispatchInfo>
			+ GetDispatchInfo
			+ codec::Decode
			+ IsType<<Self as frame_system::Config>::RuntimeCall>;

		/// Filter that is applied to calls dispatched by contracts.
		///
		/// Use this filter to control which dispatchables are callable by contracts.
		/// This is applied in **addition** to [`frame_system::Config::BaseCallFilter`].
		/// It is recommended to treat this as a whitelist.
		///
		/// # Stability
		///
		/// The runtime **must** make sure that all dispatchables that are callable by
		/// contracts remain stable. In addition [`Self::RuntimeCall`] itself must remain stable.
		/// This means that no existing variants are allowed to switch their positions.
		///
		/// # Note
		///
		/// Note that dispatchables that are called via contracts do not spawn their
		/// own wasm instance for each call (as opposed to when called via a transaction).
		/// Therefore please make sure to be restrictive about which dispatchables are allowed
		/// in order to not introduce a new DoS vector like memory allocation patterns that can
		/// be exploited to drive the runtime into a panic.
		type CallFilter: Contains<<Self as frame_system::Config>::RuntimeCall>;

		/// Used to answer contracts' queries regarding the current weight price. This is **not**
		/// used to calculate the actual fee and is only for informational purposes.
		type WeightPrice: Convert<Weight, BalanceOf<Self>>;

		/// Describes the weights of the dispatchables of this module and is also used to
		/// construct a default cost schedule.
		type WeightInfo: WeightInfo;

		/// Type that allows the runtime authors to add new host functions for a contract to call.
		type ChainExtension: chain_extension::ChainExtension<Self> + Default;

		/// Cost schedule and limits.
		#[pallet::constant]
		type Schedule: Get<Schedule<Self>>;

		/// The type of the call stack determines the maximum nesting depth of contract calls.
		///
		/// The allowed depth is `CallStack::size() + 1`.
		/// Therefore a size of `0` means that a contract cannot use call or instantiate.
		/// In other words only the origin called "root contract" is allowed to execute then.
		///
		/// This setting along with [`MaxCodeLen`](#associatedtype.MaxCodeLen) directly affects
		/// memory usage of your runtime.
		type CallStack: Array<Item = Frame<Self>>;

		/// The amount of balance a caller has to pay for each byte of storage.
		///
		/// # Note
		///
		/// Changing this value for an existing chain might need a storage migration.
		#[pallet::constant]
		type DepositPerByte: Get<BalanceOf<Self>>;

		/// Fallback value to limit the storage deposit if it's not being set by the caller.
		#[pallet::constant]
		type DefaultDepositLimit: Get<BalanceOf<Self>>;

		/// The amount of balance a caller has to pay for each storage item.
		///
		/// # Note
		///
		/// Changing this value for an existing chain might need a storage migration.
		#[pallet::constant]
		type DepositPerItem: Get<BalanceOf<Self>>;

		/// The address generator used to generate the addresses of contracts.
		type AddressGenerator: AddressGenerator<Self>;

		/// The maximum length of a contract code in bytes. This limit applies to the instrumented
		/// version of the code. Therefore `instantiate_with_code` can fail even when supplying
		/// a wasm binary below this maximum size.
		///
		/// The value should be chosen carefully taking into the account the overall memory limit
		/// your runtime has, as well as the [maximum allowed callstack
		/// depth](#associatedtype.CallStack). Look into the `integrity_test()` for some insights.
		#[pallet::constant]
		type MaxCodeLen: Get<u32>;

		/// The maximum allowable length in bytes for storage keys.
		#[pallet::constant]
		type MaxStorageKeyLen: Get<u32>;

		/// Make contract callable functions marked as `#[unstable]` available.
		///
		/// Contracts that use `#[unstable]` functions won't be able to be uploaded unless
		/// this is set to `true`. This is only meant for testnets and dev nodes in order to
		/// experiment with new features.
		///
		/// # Warning
		///
		/// Do **not** set to `true` on productions chains.
		#[pallet::constant]
		type UnsafeUnstableInterface: Get<bool>;

		/// The maximum length of the debug buffer in bytes.
		#[pallet::constant]
		type MaxDebugBufferLen: Get<u32>;

		/// The sequence of migration steps that will be applied during a migration.
		///
		/// # Examples
		/// ```
		/// use pallet_contracts::migration::{v9, v10, v11};
		/// # struct Runtime {};
		/// type Migrations = (v9::Migration<Runtime>, v10::Migration<Runtime>, v11::Migration<Runtime>);
		/// ```
		type Migrations: MigrateSequence;
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_idle(_block: T::BlockNumber, remaining_weight: Weight) -> Weight {
			use migration::MigrateResult::*;

			let (result, weight) = Migration::<T>::migrate(remaining_weight);
			let remaining_weight = remaining_weight.saturating_sub(weight);

			if !matches!(result, Completed | NoMigrationInProgress) {
				return weight
			}

			ContractInfo::<T>::process_deletion_queue_batch(remaining_weight)
				.saturating_add(T::WeightInfo::on_process_deletion_queue_batch())
		}

		fn integrity_test() {
			Migration::<T>::integrity_test();

			// Total runtime memory limit
			let max_runtime_mem: u32 = T::Schedule::get().limits.runtime_memory;
			// Memory limits for a single contract:
			// Value stack size: 1Mb per contract, default defined in wasmi
			const MAX_STACK_SIZE: u32 = 1024 * 1024;
			// Heap limit is normally 16 mempages of 64kb each = 1Mb per contract
			let max_heap_size = T::Schedule::get().limits.max_memory_size();
			// Max call depth is CallStack::size() + 1
			let max_call_depth = u32::try_from(T::CallStack::size().saturating_add(1))
				.expect("CallStack size is too big");

			// Check that given configured `MaxCodeLen`, runtime heap memory limit can't be broken.
			//
			// In worst case, the decoded wasm contract code would be `x16` times larger than the
			// encoded one. This is because even a single-byte wasm instruction has 16-byte size in
			// wasmi. This gives us `MaxCodeLen*16` safety margin.
			//
			// Next, the pallet keeps both the original and instrumented wasm blobs for each
			// contract, hence we add up `MaxCodeLen*2` more to the safety margin.
			//
			// Finally, the inefficiencies of the freeing-bump allocator
			// being used in the client for the runtime memory allocations, could lead to possible
			// memory allocations for contract code grow up to `x4` times in some extreme cases,
			// which gives us total multiplier of `18*4` for `MaxCodeLen`.
			//
			// That being said, for every contract executed in runtime, at least `MaxCodeLen*18*4`
			// memory should be available. Note that maximum allowed heap memory and stack size per
			// each contract (stack frame) should also be counted.
			//
			// Finally, we allow 50% of the runtime memory to be utilized by the contracts call
			// stack, keeping the rest for other facilities, such as PoV, etc.
			//
			// This gives us the following formula:
			//
			// `(MaxCodeLen * 18 * 4 + MAX_STACK_SIZE + max_heap_size) * max_call_depth <
			// max_runtime_mem/2`
			//
			// Hence the upper limit for the `MaxCodeLen` can be defined as follows:
			let code_len_limit = max_runtime_mem
				.saturating_div(2)
				.saturating_div(max_call_depth)
				.saturating_sub(max_heap_size)
				.saturating_sub(MAX_STACK_SIZE)
				.saturating_div(18 * 4);

			assert!(
				T::MaxCodeLen::get() < code_len_limit,
				"Given `CallStack` height {:?}, `MaxCodeLen` should be set less than {:?} \
				 (current value is {:?}), to avoid possible runtime oom issues.",
				max_call_depth,
				code_len_limit,
				T::MaxCodeLen::get(),
			);

			// Debug buffer should at least be large enough to accommodate a simple error message
			const MIN_DEBUG_BUF_SIZE: u32 = 256;
			assert!(
				T::MaxDebugBufferLen::get() > MIN_DEBUG_BUF_SIZE,
				"Debug buffer should have minimum size of {} (current setting is {})",
				MIN_DEBUG_BUF_SIZE,
				T::MaxDebugBufferLen::get(),
			)
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		<BalanceOf<T> as HasCompact>::Type: Clone + Eq + PartialEq + Debug + TypeInfo + Encode,
	{
		/// Deprecated version if [`Self::call`] for use in an in-storage `Call`.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::call().saturating_add(<Pallet<T>>::compat_weight_limit(*gas_limit)))]
		#[allow(deprecated)]
		#[deprecated(note = "1D weight is used in this extrinsic, please migrate to `call`")]
		pub fn call_old_weight(
			origin: OriginFor<T>,
			dest: AccountIdLookupOf<T>,
			#[pallet::compact] value: BalanceOf<T>,
			#[pallet::compact] gas_limit: OldWeight,
			storage_deposit_limit: Option<<BalanceOf<T> as codec::HasCompact>::Type>,
			data: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			Self::call(
				origin,
				dest,
				value,
				<Pallet<T>>::compat_weight_limit(gas_limit),
				storage_deposit_limit,
				data,
			)
		}

		/// Deprecated version if [`Self::instantiate_with_code`] for use in an in-storage `Call`.
		#[pallet::call_index(1)]
		#[pallet::weight(
			T::WeightInfo::instantiate_with_code(code.len() as u32, data.len() as u32, salt.len() as u32)
			.saturating_add(<Pallet<T>>::compat_weight_limit(*gas_limit))
		)]
		#[allow(deprecated)]
		#[deprecated(
			note = "1D weight is used in this extrinsic, please migrate to `instantiate_with_code`"
		)]
		pub fn instantiate_with_code_old_weight(
			origin: OriginFor<T>,
			#[pallet::compact] value: BalanceOf<T>,
			#[pallet::compact] gas_limit: OldWeight,
			storage_deposit_limit: Option<<BalanceOf<T> as codec::HasCompact>::Type>,
			code: Vec<u8>,
			data: Vec<u8>,
			salt: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			Self::instantiate_with_code(
				origin,
				value,
				<Pallet<T>>::compat_weight_limit(gas_limit),
				storage_deposit_limit,
				code,
				data,
				salt,
			)
		}

		/// Deprecated version if [`Self::instantiate`] for use in an in-storage `Call`.
		#[pallet::call_index(2)]
		#[pallet::weight(
			T::WeightInfo::instantiate(data.len() as u32, salt.len() as u32).saturating_add(<Pallet<T>>::compat_weight_limit(*gas_limit))
		)]
		#[allow(deprecated)]
		#[deprecated(note = "1D weight is used in this extrinsic, please migrate to `instantiate`")]
		pub fn instantiate_old_weight(
			origin: OriginFor<T>,
			#[pallet::compact] value: BalanceOf<T>,
			#[pallet::compact] gas_limit: OldWeight,
			storage_deposit_limit: Option<<BalanceOf<T> as codec::HasCompact>::Type>,
			code_hash: CodeHash<T>,
			data: Vec<u8>,
			salt: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			Self::instantiate(
				origin,
				value,
				<Pallet<T>>::compat_weight_limit(gas_limit),
				storage_deposit_limit,
				code_hash,
				data,
				salt,
			)
		}

		/// Upload new `code` without instantiating a contract from it.
		///
		/// If the code does not already exist a deposit is reserved from the caller
		/// and unreserved only when [`Self::remove_code`] is called. The size of the reserve
		/// depends on the instrumented size of the the supplied `code`.
		///
		/// If the code already exists in storage it will still return `Ok` and upgrades
		/// the in storage version to the current
		/// [`InstructionWeights::version`](InstructionWeights).
		///
		/// - `determinism`: If this is set to any other value but [`Determinism::Enforced`] then
		///   the only way to use this code is to delegate call into it from an offchain execution.
		///   Set to [`Determinism::Enforced`] if in doubt.
		///
		/// # Note
		///
		/// Anyone can instantiate a contract from any uploaded code and thus prevent its removal.
		/// To avoid this situation a constructor could employ access control so that it can
		/// only be instantiated by permissioned entities. The same is true when uploading
		/// through [`Self::instantiate_with_code`].
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::upload_code(code.len() as u32))]
		pub fn upload_code(
			origin: OriginFor<T>,
			code: Vec<u8>,
			storage_deposit_limit: Option<<BalanceOf<T> as codec::HasCompact>::Type>,
			determinism: Determinism,
		) -> DispatchResult {
			Migration::<T>::ensure_migrated()?;
			let origin = ensure_signed(origin)?;
			Self::bare_upload_code(origin, code, storage_deposit_limit.map(Into::into), determinism)
				.map(|_| ())
		}

		/// Remove the code stored under `code_hash` and refund the deposit to its owner.
		///
		/// A code can only be removed by its original uploader (its owner) and only if it is
		/// not used by any contract.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::remove_code())]
		pub fn remove_code(
			origin: OriginFor<T>,
			code_hash: CodeHash<T>,
		) -> DispatchResultWithPostInfo {
			Migration::<T>::ensure_migrated()?;
			let origin = ensure_signed(origin)?;
			<PrefabWasmModule<T>>::remove(&origin, code_hash)?;
			// we waive the fee because removing unused code is beneficial
			Ok(Pays::No.into())
		}

		/// Privileged function that changes the code of an existing contract.
		///
		/// This takes care of updating refcounts and all other necessary operations. Returns
		/// an error if either the `code_hash` or `dest` do not exist.
		///
		/// # Note
		///
		/// This does **not** change the address of the contract in question. This means
		/// that the contract address is no longer derived from its code hash after calling
		/// this dispatchable.
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::set_code())]
		pub fn set_code(
			origin: OriginFor<T>,
			dest: AccountIdLookupOf<T>,
			code_hash: CodeHash<T>,
		) -> DispatchResult {
			Migration::<T>::ensure_migrated()?;
			ensure_root(origin)?;
			let dest = T::Lookup::lookup(dest)?;
			<ContractInfoOf<T>>::try_mutate(&dest, |contract| {
				let contract = if let Some(contract) = contract {
					contract
				} else {
					return Err(<Error<T>>::ContractNotFound.into())
				};
				<PrefabWasmModule<T>>::add_user(code_hash)?;
				<PrefabWasmModule<T>>::remove_user(contract.code_hash);
				Self::deposit_event(
					vec![T::Hashing::hash_of(&dest), code_hash, contract.code_hash],
					Event::ContractCodeUpdated {
						contract: dest.clone(),
						new_code_hash: code_hash,
						old_code_hash: contract.code_hash,
					},
				);
				contract.code_hash = code_hash;
				Ok(())
			})
		}

		/// Makes a call to an account, optionally transferring some balance.
		///
		/// # Parameters
		///
		/// * `dest`: Address of the contract to call.
		/// * `value`: The balance to transfer from the `origin` to `dest`.
		/// * `gas_limit`: The gas limit enforced when executing the constructor.
		/// * `storage_deposit_limit`: The maximum amount of balance that can be charged from the
		///   caller to pay for the storage consumed.
		/// * `data`: The input data to pass to the contract.
		///
		/// * If the account is a smart-contract account, the associated code will be
		/// executed and any value will be transferred.
		/// * If the account is a regular account, any value will be transferred.
		/// * If no account exists and the call value is not less than `existential_deposit`,
		/// a regular account will be created and any value will be transferred.
		#[pallet::call_index(6)]
		#[pallet::weight(T::WeightInfo::call().saturating_add(*gas_limit))]
		pub fn call(
			origin: OriginFor<T>,
			dest: AccountIdLookupOf<T>,
			#[pallet::compact] value: BalanceOf<T>,
			gas_limit: Weight,
			storage_deposit_limit: Option<<BalanceOf<T> as codec::HasCompact>::Type>,
			data: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			Migration::<T>::ensure_migrated()?;
			let common = CommonInput {
				origin: Origin::from_runtime_origin(origin)?,
				value,
				data,
				gas_limit: gas_limit.into(),
				storage_deposit_limit: storage_deposit_limit.map(Into::into),
				debug_message: None,
			};
			let dest = T::Lookup::lookup(dest)?;
			let mut output =
				CallInput::<T> { dest, determinism: Determinism::Enforced }.run_guarded(common);
			if let Ok(retval) = &output.result {
				if retval.did_revert() {
					output.result = Err(<Error<T>>::ContractReverted.into());
				}
			}
			output.gas_meter.into_dispatch_result(output.result, T::WeightInfo::call())
		}

		/// Instantiates a new contract from the supplied `code` optionally transferring
		/// some balance.
		///
		/// This dispatchable has the same effect as calling [`Self::upload_code`] +
		/// [`Self::instantiate`]. Bundling them together provides efficiency gains. Please
		/// also check the documentation of [`Self::upload_code`].
		///
		/// # Parameters
		///
		/// * `value`: The balance to transfer from the `origin` to the newly created contract.
		/// * `gas_limit`: The gas limit enforced when executing the constructor.
		/// * `storage_deposit_limit`: The maximum amount of balance that can be charged/reserved
		///   from the caller to pay for the storage consumed.
		/// * `code`: The contract code to deploy in raw bytes.
		/// * `data`: The input data to pass to the contract constructor.
		/// * `salt`: Used for the address derivation. See [`Pallet::contract_address`].
		///
		/// Instantiation is executed as follows:
		///
		/// - The supplied `code` is instrumented, deployed, and a `code_hash` is created for that
		///   code.
		/// - If the `code_hash` already exists on the chain the underlying `code` will be shared.
		/// - The destination address is computed based on the sender, code_hash and the salt.
		/// - The smart-contract account is created at the computed address.
		/// - The `value` is transferred to the new account.
		/// - The `deploy` function is executed in the context of the newly-created account.
		#[pallet::call_index(7)]
		#[pallet::weight(
			T::WeightInfo::instantiate_with_code(code.len() as u32, data.len() as u32, salt.len() as u32)
			.saturating_add(*gas_limit)
		)]
		pub fn instantiate_with_code(
			origin: OriginFor<T>,
			#[pallet::compact] value: BalanceOf<T>,
			gas_limit: Weight,
			storage_deposit_limit: Option<<BalanceOf<T> as codec::HasCompact>::Type>,
			code: Vec<u8>,
			data: Vec<u8>,
			salt: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			Migration::<T>::ensure_migrated()?;
			let code_len = code.len() as u32;
			let data_len = data.len() as u32;
			let salt_len = salt.len() as u32;
			let common = CommonInput {
				origin: Origin::from_runtime_origin(origin)?,
				value,
				data,
				gas_limit,
				storage_deposit_limit: storage_deposit_limit.map(Into::into),
				debug_message: None,
			};
			let mut output =
				InstantiateInput::<T> { code: Code::Upload(code), salt }.run_guarded(common);
			if let Ok(retval) = &output.result {
				if retval.1.did_revert() {
					output.result = Err(<Error<T>>::ContractReverted.into());
				}
			}
			output.gas_meter.into_dispatch_result(
				output.result.map(|(_address, result)| result),
				T::WeightInfo::instantiate_with_code(code_len, data_len, salt_len),
			)
		}

		/// Instantiates a contract from a previously deployed wasm binary.
		///
		/// This function is identical to [`Self::instantiate_with_code`] but without the
		/// code deployment step. Instead, the `code_hash` of an on-chain deployed wasm binary
		/// must be supplied.
		#[pallet::call_index(8)]
		#[pallet::weight(
			T::WeightInfo::instantiate(data.len() as u32, salt.len() as u32).saturating_add(*gas_limit)
		)]
		pub fn instantiate(
			origin: OriginFor<T>,
			#[pallet::compact] value: BalanceOf<T>,
			gas_limit: Weight,
			storage_deposit_limit: Option<<BalanceOf<T> as codec::HasCompact>::Type>,
			code_hash: CodeHash<T>,
			data: Vec<u8>,
			salt: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			Migration::<T>::ensure_migrated()?;
			let data_len = data.len() as u32;
			let salt_len = salt.len() as u32;
			let common = CommonInput {
				origin: Origin::from_runtime_origin(origin)?,
				value,
				data,
				gas_limit,
				storage_deposit_limit: storage_deposit_limit.map(Into::into),
				debug_message: None,
			};
			let mut output =
				InstantiateInput::<T> { code: Code::Existing(code_hash), salt }.run_guarded(common);
			if let Ok(retval) = &output.result {
				if retval.1.did_revert() {
					output.result = Err(<Error<T>>::ContractReverted.into());
				}
			}
			output.gas_meter.into_dispatch_result(
				output.result.map(|(_address, output)| output),
				T::WeightInfo::instantiate(data_len, salt_len),
			)
		}

		/// When a migration is in progress, this dispatchable can be used to run migration steps.
		/// Calls that contribute to advancing the migration have their fees waived, as it's helpful
		/// for the chain. Note that while the migration is in progress, the pallet will also
		/// leverage the `on_idle` hooks to run migration steps.
		#[pallet::call_index(9)]
		#[pallet::weight(T::WeightInfo::migrate().saturating_add(*weight_limit))]
		pub fn migrate(origin: OriginFor<T>, weight_limit: Weight) -> DispatchResultWithPostInfo {
			use migration::MigrateResult::*;
			ensure_signed(origin)?;

			let weight_limit = weight_limit.saturating_add(T::WeightInfo::migrate());
			let (result, weight) = Migration::<T>::migrate(weight_limit);

			match result {
				Completed =>
					Ok(PostDispatchInfo { actual_weight: Some(weight), pays_fee: Pays::No }),
				InProgress { steps_done, .. } if steps_done > 0 =>
					Ok(PostDispatchInfo { actual_weight: Some(weight), pays_fee: Pays::No }),
				InProgress { .. } =>
					Ok(PostDispatchInfo { actual_weight: Some(weight), pays_fee: Pays::Yes }),
				NoMigrationInProgress | NoMigrationPerformed => {
					let err: DispatchError = <Error<T>>::NoMigrationPerformed.into();
					Err(err.with_weight(T::WeightInfo::migrate()))
				},
			}
		}
	}

	#[pallet::event]
	pub enum Event<T: Config> {
		/// Contract deployed by address at the specified address.
		Instantiated { deployer: T::AccountId, contract: T::AccountId },

		/// Contract has been removed.
		///
		/// # Note
		///
		/// The only way for a contract to be removed and emitting this event is by calling
		/// `seal_terminate`.
		Terminated {
			/// The contract that was terminated.
			contract: T::AccountId,
			/// The account that received the contracts remaining balance
			beneficiary: T::AccountId,
		},

		/// Code with the specified hash has been stored.
		CodeStored { code_hash: T::Hash },

		/// A custom event emitted by the contract.
		ContractEmitted {
			/// The contract that emitted the event.
			contract: T::AccountId,
			/// Data supplied by the contract. Metadata generated during contract compilation
			/// is needed to decode it.
			data: Vec<u8>,
		},

		/// A code with the specified hash was removed.
		CodeRemoved { code_hash: T::Hash },

		/// A contract's code was updated.
		ContractCodeUpdated {
			/// The contract that has been updated.
			contract: T::AccountId,
			/// New code hash that was set for the contract.
			new_code_hash: T::Hash,
			/// Previous code hash of the contract.
			old_code_hash: T::Hash,
		},

		/// A contract was called either by a plain account or another contract.
		///
		/// # Note
		///
		/// Please keep in mind that like all events this is only emitted for successful
		/// calls. This is because on failure all storage changes including events are
		/// rolled back.
		Called {
			/// The caller of the `contract`.
			caller: Origin<T>,
			/// The contract that was called.
			contract: T::AccountId,
		},

		/// A contract delegate called a code hash.
		///
		/// # Note
		///
		/// Please keep in mind that like all events this is only emitted for successful
		/// calls. This is because on failure all storage changes including events are
		/// rolled back.
		DelegateCalled {
			/// The contract that performed the delegate call and hence in whose context
			/// the `code_hash` is executed.
			contract: T::AccountId,
			/// The code hash that was delegate called.
			code_hash: CodeHash<T>,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// A new schedule must have a greater version than the current one.
		InvalidScheduleVersion,
		/// Invalid combination of flags supplied to `seal_call` or `seal_delegate_call`.
		InvalidCallFlags,
		/// The executed contract exhausted its gas limit.
		OutOfGas,
		/// The output buffer supplied to a contract API call was too small.
		OutputBufferTooSmall,
		/// Performing the requested transfer failed. Probably because there isn't enough
		/// free balance in the sender's account.
		TransferFailed,
		/// Performing a call was denied because the calling depth reached the limit
		/// of what is specified in the schedule.
		MaxCallDepthReached,
		/// No contract was found at the specified address.
		ContractNotFound,
		/// The code supplied to `instantiate_with_code` exceeds the limit specified in the
		/// current schedule.
		CodeTooLarge,
		/// No code could be found at the supplied code hash.
		CodeNotFound,
		/// A buffer outside of sandbox memory was passed to a contract API function.
		OutOfBounds,
		/// Input passed to a contract API function failed to decode as expected type.
		DecodingFailed,
		/// Contract trapped during execution.
		ContractTrapped,
		/// The size defined in `T::MaxValueSize` was exceeded.
		ValueTooLarge,
		/// Termination of a contract is not allowed while the contract is already
		/// on the call stack. Can be triggered by `seal_terminate`.
		TerminatedWhileReentrant,
		/// `seal_call` forwarded this contracts input. It therefore is no longer available.
		InputForwarded,
		/// The subject passed to `seal_random` exceeds the limit.
		RandomSubjectTooLong,
		/// The amount of topics passed to `seal_deposit_events` exceeds the limit.
		TooManyTopics,
		/// The chain does not provide a chain extension. Calling the chain extension results
		/// in this error. Note that this usually  shouldn't happen as deploying such contracts
		/// is rejected.
		NoChainExtension,
		/// A contract with the same AccountId already exists.
		DuplicateContract,
		/// A contract self destructed in its constructor.
		///
		/// This can be triggered by a call to `seal_terminate`.
		TerminatedInConstructor,
		/// A call tried to invoke a contract that is flagged as non-reentrant.
		/// The only other cause is that a call from a contract into the runtime tried to call back
		/// into `pallet-contracts`. This would make the whole pallet reentrant with regard to
		/// contract code execution which is not supported.
		ReentranceDenied,
		/// Origin doesn't have enough balance to pay the required storage deposits.
		StorageDepositNotEnoughFunds,
		/// More storage was created than allowed by the storage deposit limit.
		StorageDepositLimitExhausted,
		/// Code removal was denied because the code is still in use by at least one contract.
		CodeInUse,
		/// The contract ran to completion but decided to revert its storage changes.
		/// Please note that this error is only returned from extrinsics. When called directly
		/// or via RPC an `Ok` will be returned. In this case the caller needs to inspect the flags
		/// to determine whether a reversion has taken place.
		ContractReverted,
		/// The contract's code was found to be invalid during validation or instrumentation.
		///
		/// The most likely cause of this is that an API was used which is not supported by the
		/// node. This happens if an older node is used with a new version of ink!. Try updating
		/// your node to the newest available version.
		///
		/// A more detailed error can be found on the node console if debug messages are enabled
		/// by supplying `-lruntime::contracts=debug`.
		CodeRejected,
		/// An indetermistic code was used in a context where this is not permitted.
		Indeterministic,
		/// A pending migration needs to complete before the extrinsic can be called.
		MigrationInProgress,
		/// Migrate dispatch call was attempted but no migration was performed.
		NoMigrationPerformed,
	}

	/// A mapping from an original code hash to the original code, untouched by instrumentation.
	#[pallet::storage]
	pub(crate) type PristineCode<T: Config> = StorageMap<_, Identity, CodeHash<T>, CodeVec<T>>;

	/// A mapping between an original code hash and instrumented wasm code, ready for execution.
	#[pallet::storage]
	pub(crate) type CodeStorage<T: Config> =
		StorageMap<_, Identity, CodeHash<T>, PrefabWasmModule<T>>;

	/// A mapping between an original code hash and its owner information.
	#[pallet::storage]
	pub(crate) type OwnerInfoOf<T: Config> = StorageMap<_, Identity, CodeHash<T>, OwnerInfo<T>>;

	/// This is a **monotonic** counter incremented on contract instantiation.
	///
	/// This is used in order to generate unique trie ids for contracts.
	/// The trie id of a new contract is calculated from hash(account_id, nonce).
	/// The nonce is required because otherwise the following sequence would lead to
	/// a possible collision of storage:
	///
	/// 1. Create a new contract.
	/// 2. Terminate the contract.
	/// 3. Immediately recreate the contract with the same account_id.
	///
	/// This is bad because the contents of a trie are deleted lazily and there might be
	/// storage of the old instantiation still in it when the new contract is created. Please
	/// note that we can't replace the counter by the block number because the sequence above
	/// can happen in the same block. We also can't keep the account counter in memory only
	/// because storage is the only way to communicate across different extrinsics in the
	/// same block.
	///
	/// # Note
	///
	/// Do not use it to determine the number of contracts. It won't be decremented if
	/// a contract is destroyed.
	#[pallet::storage]
	pub(crate) type Nonce<T: Config> = StorageValue<_, u64, ValueQuery>;

	/// The code associated with a given account.
	///
	/// TWOX-NOTE: SAFE since `AccountId` is a secure hash.
	#[pallet::storage]
	pub(crate) type ContractInfoOf<T: Config> =
		StorageMap<_, Twox64Concat, T::AccountId, ContractInfo<T>>;

	/// Evicted contracts that await child trie deletion.
	///
	/// Child trie deletion is a heavy operation depending on the amount of storage items
	/// stored in said trie. Therefore this operation is performed lazily in `on_idle`.
	#[pallet::storage]
	pub(crate) type DeletionQueue<T: Config> = StorageMap<_, Twox64Concat, u32, TrieId>;

	/// A pair of monotonic counters used to track the latest contract marked for deletion
	/// and the latest deleted contract in queue.
	#[pallet::storage]
	pub(crate) type DeletionQueueCounter<T: Config> =
		StorageValue<_, DeletionQueueManager<T>, ValueQuery>;

	#[pallet::storage]
	pub(crate) type MigrationInProgress<T: Config> =
		StorageValue<_, migration::Cursor, OptionQuery>;
}

/// The type of origins supported by the contracts pallet.
#[derive(Clone, Encode, Decode, PartialEq, TypeInfo, RuntimeDebugNoBound)]
pub enum Origin<T: Config> {
	Root,
	Signed(T::AccountId),
}

impl<T: Config> Origin<T> {
	/// Creates a new Signed Caller from an AccountId.
	pub fn from_account_id(account_id: T::AccountId) -> Self {
		Origin::Signed(account_id)
	}
	/// Creates a new Origin from a `RuntimeOrigin`.
	pub fn from_runtime_origin(o: OriginFor<T>) -> Result<Self, DispatchError> {
		match o.into() {
			Ok(RawOrigin::Root) => Ok(Self::Root),
			Ok(RawOrigin::Signed(t)) => Ok(Self::Signed(t)),
			_ => Err(BadOrigin.into()),
		}
	}
	/// Returns the AccountId of a Signed Origin or an error if the origin is Root.
	pub fn account_id(&self) -> Result<&T::AccountId, DispatchError> {
		match self {
			Origin::Signed(id) => Ok(id),
			Origin::Root => Err(DispatchError::RootNotAllowed),
		}
	}
}

/// Context of a contract invocation.
struct CommonInput<'a, T: Config> {
	origin: Origin<T>,
	value: BalanceOf<T>,
	data: Vec<u8>,
	gas_limit: Weight,
	storage_deposit_limit: Option<BalanceOf<T>>,
	debug_message: Option<&'a mut DebugBufferVec<T>>,
}

/// Input specific to a call into contract.
struct CallInput<T: Config> {
	dest: T::AccountId,
	determinism: Determinism,
}

/// Input specific to a contract instantiation invocation.
struct InstantiateInput<T: Config> {
	code: Code<CodeHash<T>>,
	salt: Vec<u8>,
}

/// Determines whether events should be collected during execution.
#[derive(PartialEq)]
pub enum CollectEvents {
	/// Collect events.
	///
	/// # Note
	///
	/// Events should only be collected when called off-chain, as this would otherwise
	/// collect all the Events emitted in the block so far and put them into the PoV.
	///
	/// **Never** use this mode for on-chain execution.
	UnsafeCollect,
	/// Skip event collection.
	Skip,
}

/// Determines whether debug messages will be collected.
#[derive(PartialEq)]
pub enum DebugInfo {
	/// Collect debug messages.
	/// # Note
	///
	/// This should only ever be set to `UnsafeDebug` when executing as an RPC because
	/// it adds allocations and could be abused to drive the runtime into an OOM panic.
	UnsafeDebug,
	/// Skip collection of debug messages.
	Skip,
}

/// Return type of private helper functions.
struct InternalOutput<T: Config, O> {
	/// The gas meter that was used to execute the call.
	gas_meter: GasMeter<T>,
	/// The storage deposit used by the call.
	storage_deposit: StorageDeposit<BalanceOf<T>>,
	/// The result of the call.
	result: Result<O, ExecError>,
}

/// Helper trait to wrap contract execution entry points into a single function
/// [`Invokable::run_guarded`].
trait Invokable<T: Config> {
	/// What is returned as a result of a successful invocation.
	type Output;

	/// Single entry point to contract execution.
	/// Downstream execution flow is branched by implementations of [`Invokable`] trait:
	///
	/// - [`InstantiateInput::run`] runs contract instantiation,
	/// - [`CallInput::run`] runs contract call.
	///
	/// We enforce a re-entrancy guard here by initializing and checking a boolean flag through a
	/// global reference.
	fn run_guarded(&self, common: CommonInput<T>) -> InternalOutput<T, Self::Output> {
		// Set up a global reference to the boolean flag used for the re-entrancy guard.
		environmental!(executing_contract: bool);

		let gas_limit = common.gas_limit;

		// Check whether the origin is allowed here. The logic of the access rules
		// is in the `ensure_origin`, this could vary for different implementations of this
		// trait. For example, some actions might not allow Root origin as they could require an
		// AccountId associated with the origin.
		if let Err(e) = self.ensure_origin(common.origin.clone()) {
			return InternalOutput {
				gas_meter: GasMeter::new(gas_limit),
				storage_deposit: Default::default(),
				result: Err(ExecError { error: e.into(), origin: ErrorOrigin::Caller }),
			}
		}

		executing_contract::using_once(&mut false, || {
			executing_contract::with(|f| {
				// Fail if already entered contract execution
				if *f {
					return Err(())
				}
				// We are entering contract execution
				*f = true;
				Ok(())
			})
			.expect("Returns `Ok` if called within `using_once`. It is syntactically obvious that this is the case; qed")
			.map_or_else(
				|_| InternalOutput {
					gas_meter: GasMeter::new(gas_limit),
					storage_deposit: Default::default(),
					result: Err(ExecError {
						error: <Error<T>>::ReentranceDenied.into(),
						origin: ErrorOrigin::Caller,
					}),
				},
				// Enter contract call.
				|_| self.run(common, GasMeter::new(gas_limit)),
			)
		})
	}

	/// Method that does the actual call to a contract. It can be either a call to a deployed
	/// contract or a instantiation of a new one.
	///
	/// Called by dispatchables and public functions through the [`Invokable::run_guarded`].
	fn run(
		&self,
		common: CommonInput<T>,
		gas_meter: GasMeter<T>,
	) -> InternalOutput<T, Self::Output>;

	/// This method ensures that the given `origin` is allowed to invoke the current `Invokable`.
	///
	/// Called by dispatchables and public functions through the [`Invokable::run_guarded`].
	fn ensure_origin(&self, origin: Origin<T>) -> Result<(), DispatchError>;
}

impl<T: Config> Invokable<T> for CallInput<T> {
	type Output = ExecReturnValue;

	fn run(
		&self,
		common: CommonInput<T>,
		mut gas_meter: GasMeter<T>,
	) -> InternalOutput<T, Self::Output> {
		let CallInput { dest, determinism } = self;
		let CommonInput { origin, value, data, debug_message, .. } = common;
		let mut storage_meter =
			match StorageMeter::new(&origin, common.storage_deposit_limit, common.value) {
				Ok(meter) => meter,
				Err(err) =>
					return InternalOutput {
						result: Err(err.into()),
						gas_meter,
						storage_deposit: Default::default(),
					},
			};
		let schedule = T::Schedule::get();
		let result = ExecStack::<T, PrefabWasmModule<T>>::run_call(
			origin.clone(),
			dest.clone(),
			&mut gas_meter,
			&mut storage_meter,
			&schedule,
			value,
			data.clone(),
			debug_message,
			*determinism,
		);

		match storage_meter.try_into_deposit(&origin) {
			Ok(storage_deposit) => InternalOutput { gas_meter, storage_deposit, result },
			Err(err) => InternalOutput {
				gas_meter,
				storage_deposit: Default::default(),
				result: Err(err.into()),
			},
		}
	}

	fn ensure_origin(&self, _origin: Origin<T>) -> Result<(), DispatchError> {
		Ok(())
	}
}

impl<T: Config> Invokable<T> for InstantiateInput<T> {
	type Output = (AccountIdOf<T>, ExecReturnValue);

	fn run(
		&self,
		mut common: CommonInput<T>,
		mut gas_meter: GasMeter<T>,
	) -> InternalOutput<T, Self::Output> {
		let mut storage_deposit = Default::default();
		let try_exec = || {
			let schedule = T::Schedule::get();
			let InstantiateInput { salt, .. } = self;
			let CommonInput { origin: contract_origin, .. } = common;
			let origin = contract_origin.account_id()?;
			let (extra_deposit, executable) = match &self.code {
				Code::Upload(binary) => {
					let executable = PrefabWasmModule::from_code(
						binary.clone(),
						&schedule,
						origin.clone(),
						Determinism::Enforced,
						TryInstantiate::Skip,
					)
					.map_err(|(err, msg)| {
						common
							.debug_message
							.as_mut()
							.map(|buffer| buffer.try_extend(&mut msg.bytes()));
						err
					})?;
					// The open deposit will be charged during execution when the
					// uploaded module does not already exist. This deposit is not part of the
					// storage meter because it is not transferred to the contract but
					// reserved on the uploading account.
					(executable.open_deposit(), executable)
				},
				Code::Existing(hash) => (
					Default::default(),
					PrefabWasmModule::from_storage(*hash, &schedule, &mut gas_meter)?,
				),
			};
			let contract_origin = Origin::from_account_id(origin.clone());
			let mut storage_meter = StorageMeter::new(
				&contract_origin,
				common.storage_deposit_limit,
				common.value.saturating_add(extra_deposit),
			)?;
			let CommonInput { value, data, debug_message, .. } = common;
			let result = ExecStack::<T, PrefabWasmModule<T>>::run_instantiate(
				origin.clone(),
				executable,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				value,
				data.clone(),
				&salt,
				debug_message,
			);

			storage_deposit = storage_meter
				.try_into_deposit(&contract_origin)?
				.saturating_add(&StorageDeposit::Charge(extra_deposit));
			result
		};
		InternalOutput { result: try_exec(), gas_meter, storage_deposit }
	}

	fn ensure_origin(&self, origin: Origin<T>) -> Result<(), DispatchError> {
		match origin {
			Origin::Signed(_) => Ok(()),
			Origin::Root => Err(DispatchError::RootNotAllowed),
		}
	}
}

macro_rules! ensure_no_migration_in_progress {
	() => {
		if Migration::<T>::in_progress() {
			return ContractResult {
				gas_consumed: Zero::zero(),
				gas_required: Zero::zero(),
				storage_deposit: Default::default(),
				debug_message: Vec::new(),
				result: Err(Error::<T>::MigrationInProgress.into()),
				events: None,
			}
		}
	};
}

impl<T: Config> Pallet<T> {
	/// Perform a call to a specified contract.
	///
	/// This function is similar to [`Self::call`], but doesn't perform any address lookups
	/// and better suitable for calling directly from Rust.
	///
	/// # Note
	///
	/// If `debug` is set to `DebugInfo::UnsafeDebug` it returns additional human readable debugging
	/// information.
	///
	/// If `collect_events` is set to `CollectEvents::UnsafeCollect` it collects all the Events
	/// emitted in the block so far and the ones emitted during the execution of this contract.
	pub fn bare_call(
		origin: T::AccountId,
		dest: T::AccountId,
		value: BalanceOf<T>,
		gas_limit: Weight,
		storage_deposit_limit: Option<BalanceOf<T>>,
		data: Vec<u8>,
		debug: DebugInfo,
		collect_events: CollectEvents,
		determinism: Determinism,
	) -> ContractExecResult<BalanceOf<T>, EventRecordOf<T>> {
		ensure_no_migration_in_progress!();

		let mut debug_message = if matches!(debug, DebugInfo::UnsafeDebug) {
			Some(DebugBufferVec::<T>::default())
		} else {
			None
		};
		let origin = Origin::from_account_id(origin);
		let common = CommonInput {
			origin,
			value,
			data,
			gas_limit,
			storage_deposit_limit,
			debug_message: debug_message.as_mut(),
		};
		let output = CallInput::<T> { dest, determinism }.run_guarded(common);
		let events = if matches!(collect_events, CollectEvents::UnsafeCollect) {
			Some(System::<T>::read_events_no_consensus().map(|e| *e).collect())
		} else {
			None
		};

		ContractExecResult {
			result: output.result.map_err(|r| r.error),
			gas_consumed: output.gas_meter.gas_consumed(),
			gas_required: output.gas_meter.gas_required(),
			storage_deposit: output.storage_deposit,
			debug_message: debug_message.unwrap_or_default().to_vec(),
			events,
		}
	}

	/// Instantiate a new contract.
	///
	/// This function is similar to [`Self::instantiate`], but doesn't perform any address lookups
	/// and better suitable for calling directly from Rust.
	///
	/// It returns the execution result, account id and the amount of used weight.
	///
	/// # Note
	///
	/// If `debug` is set to `DebugInfo::UnsafeDebug` it returns additional human readable debugging
	/// information.
	///
	/// If `collect_events` is set to `CollectEvents::UnsafeCollect` it collects all the Events
	/// emitted in the block so far.
	pub fn bare_instantiate(
		origin: T::AccountId,
		value: BalanceOf<T>,
		gas_limit: Weight,
		storage_deposit_limit: Option<BalanceOf<T>>,
		code: Code<CodeHash<T>>,
		data: Vec<u8>,
		salt: Vec<u8>,
		debug: DebugInfo,
		collect_events: CollectEvents,
	) -> ContractInstantiateResult<T::AccountId, BalanceOf<T>, EventRecordOf<T>> {
		ensure_no_migration_in_progress!();

		let mut debug_message = if debug == DebugInfo::UnsafeDebug {
			Some(DebugBufferVec::<T>::default())
		} else {
			None
		};
		let common = CommonInput {
			origin: Origin::from_account_id(origin),
			value,
			data,
			gas_limit,
			storage_deposit_limit,
			debug_message: debug_message.as_mut(),
		};
		let output = InstantiateInput::<T> { code, salt }.run_guarded(common);
		// collect events if CollectEvents is UnsafeCollect
		let events = if collect_events == CollectEvents::UnsafeCollect {
			Some(System::<T>::read_events_no_consensus().map(|e| *e).collect())
		} else {
			None
		};
		ContractInstantiateResult {
			result: output
				.result
				.map(|(account_id, result)| InstantiateReturnValue { result, account_id })
				.map_err(|e| e.error),
			gas_consumed: output.gas_meter.gas_consumed(),
			gas_required: output.gas_meter.gas_required(),
			storage_deposit: output.storage_deposit,
			debug_message: debug_message.unwrap_or_default().to_vec(),
			events,
		}
	}

	/// Upload new code without instantiating a contract from it.
	///
	/// This function is similar to [`Self::upload_code`], but doesn't perform any address lookups
	/// and better suitable for calling directly from Rust.
	pub fn bare_upload_code(
		origin: T::AccountId,
		code: Vec<u8>,
		storage_deposit_limit: Option<BalanceOf<T>>,
		determinism: Determinism,
	) -> CodeUploadResult<CodeHash<T>, BalanceOf<T>> {
		Migration::<T>::ensure_migrated()?;
		let schedule = T::Schedule::get();
		let module = PrefabWasmModule::from_code(
			code,
			&schedule,
			origin,
			determinism,
			TryInstantiate::Instantiate,
		)
		.map_err(|(err, _)| err)?;
		let deposit = module.open_deposit();
		if let Some(storage_deposit_limit) = storage_deposit_limit {
			ensure!(storage_deposit_limit >= deposit, <Error<T>>::StorageDepositLimitExhausted);
		}
		let result = CodeUploadReturnValue { code_hash: *module.code_hash(), deposit };
		module.store()?;
		Ok(result)
	}

	/// Query storage of a specified contract under a specified key.
	pub fn get_storage(address: T::AccountId, key: Vec<u8>) -> GetStorageResult {
		if Migration::<T>::in_progress() {
			return Err(ContractAccessError::MigrationInProgress)
		}
		let contract_info =
			ContractInfoOf::<T>::get(&address).ok_or(ContractAccessError::DoesntExist)?;

		let maybe_value = contract_info.read(
			&Key::<T>::try_from_var(key)
				.map_err(|_| ContractAccessError::KeyDecodingFailed)?
				.into(),
		);
		Ok(maybe_value)
	}

	/// Determine the address of a contract.
	///
	/// This is the address generation function used by contract instantiation. See
	/// [`DefaultAddressGenerator`] for the default implementation.
	pub fn contract_address(
		deploying_address: &T::AccountId,
		code_hash: &CodeHash<T>,
		input_data: &[u8],
		salt: &[u8],
	) -> T::AccountId {
		T::AddressGenerator::contract_address(deploying_address, code_hash, input_data, salt)
	}

	/// Returns the code hash of the contract specified by `account` ID.
	pub fn code_hash(account: &AccountIdOf<T>) -> Option<CodeHash<T>> {
		ContractInfo::<T>::load_code_hash(account)
	}

	/// Store code for benchmarks which does not check nor instrument the code.
	#[cfg(feature = "runtime-benchmarks")]
	fn store_code_raw(
		code: Vec<u8>,
		owner: T::AccountId,
	) -> frame_support::dispatch::DispatchResult {
		let schedule = T::Schedule::get();
		PrefabWasmModule::store_code_unchecked(code, &schedule, owner)?;
		Ok(())
	}

	/// This exists so that benchmarks can determine the weight of running an instrumentation.
	#[cfg(feature = "runtime-benchmarks")]
	fn reinstrument_module(
		module: &mut PrefabWasmModule<T>,
		schedule: &Schedule<T>,
	) -> frame_support::dispatch::DispatchResult {
		self::wasm::reinstrument(module, schedule).map(|_| ())
	}

	/// Deposit a pallet contracts event. Handles the conversion to the overarching event type.
	fn deposit_event(topics: Vec<T::Hash>, event: Event<T>) {
		<frame_system::Pallet<T>>::deposit_event_indexed(
			&topics,
			<T as Config>::RuntimeEvent::from(event).into(),
		)
	}

	/// Return the existential deposit of [`Config::Currency`].
	fn min_balance() -> BalanceOf<T> {
		<T::Currency as Inspect<AccountIdOf<T>>>::minimum_balance()
	}

	/// Convert gas_limit from 1D Weight to a 2D Weight.
	///
	/// Used by backwards compatible extrinsics. We cannot just set the proof_size weight limit to
	/// zero or an old `Call` will just fail with OutOfGas.
	fn compat_weight_limit(gas_limit: OldWeight) -> Weight {
		Weight::from_parts(gas_limit, u64::from(T::MaxCodeLen::get()) * 2)
	}
}

sp_api::decl_runtime_apis! {
	/// The API used to dry-run contract interactions.
	#[api_version(2)]
	pub trait ContractsApi<AccountId, Balance, BlockNumber, Hash, EventRecord> where
		AccountId: Codec,
		Balance: Codec,
		BlockNumber: Codec,
		Hash: Codec,
		EventRecord: Codec,
	{
		/// Perform a call from a specified account to a given contract.
		///
		/// See [`crate::Pallet::bare_call`].
		fn call(
			origin: AccountId,
			dest: AccountId,
			value: Balance,
			gas_limit: Option<Weight>,
			storage_deposit_limit: Option<Balance>,
			input_data: Vec<u8>,
		) -> ContractExecResult<Balance, EventRecord>;

		/// Instantiate a new contract.
		///
		/// See `[crate::Pallet::bare_instantiate]`.
		fn instantiate(
			origin: AccountId,
			value: Balance,
			gas_limit: Option<Weight>,
			storage_deposit_limit: Option<Balance>,
			code: Code<Hash>,
			data: Vec<u8>,
			salt: Vec<u8>,
		) -> ContractInstantiateResult<AccountId, Balance, EventRecord>;

		/// Upload new code without instantiating a contract from it.
		///
		/// See [`crate::Pallet::bare_upload_code`].
		fn upload_code(
			origin: AccountId,
			code: Vec<u8>,
			storage_deposit_limit: Option<Balance>,
			determinism: Determinism,
		) -> CodeUploadResult<Hash, Balance>;

		/// Query a given storage key in a given contract.
		///
		/// Returns `Ok(Some(Vec<u8>))` if the storage value exists under the given key in the
		/// specified account and `Ok(None)` if it doesn't. If the account specified by the address
		/// doesn't exist, or doesn't have a contract then `Err` is returned.
		fn get_storage(
			address: AccountId,
			key: Vec<u8>,
		) -> GetStorageResult;
	}
}
