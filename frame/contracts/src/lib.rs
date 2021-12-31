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

//! # Contract Pallet
//!
//! The Contract module provides functionality for the runtime to deploy and execute WebAssembly
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
//! The Contract module is a work in progress. The following examples show how this Contract module
//! can be used to instantiate and call contracts.
//!
//! * [`ink`](https://github.com/paritytech/ink) is
//! an [`eDSL`](https://wiki.haskell.org/Embedded_domain_specific_language) that enables writing
//! WebAssembly based smart contracts in the Rust programming language. This is a work in progress.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "runtime-benchmarks", recursion_limit = "512")]

#[macro_use]
mod gas;
mod benchmarking;
mod exec;
mod migration;
mod schedule;
mod storage;
mod wasm;

pub mod chain_extension;
pub mod weights;

#[cfg(test)]
mod tests;

pub use crate::{
	exec::Frame,
	pallet::*,
	schedule::{HostFnWeights, InstructionWeights, Limits, Schedule},
};
use crate::{
	exec::{AccountIdOf, ExecError, Executable, Stack as ExecStack},
	gas::GasMeter,
	storage::{meter::Meter as StorageMeter, ContractInfo, DeletedContract, Storage},
	wasm::{OwnerInfo, PrefabWasmModule},
	weights::WeightInfo,
};
use codec::{Encode, HasCompact};
use frame_support::{
	dispatch::Dispatchable,
	ensure,
	traits::{Contains, Currency, Get, Randomness, ReservableCurrency, StorageVersion, Time},
	weights::{GetDispatchInfo, Pays, PostDispatchInfo, Weight},
};
use frame_system::Pallet as System;
use pallet_contracts_primitives::{
	Code, CodeUploadResult, CodeUploadReturnValue, ContractAccessError, ContractExecResult,
	ContractInstantiateResult, ExecReturnValue, GetStorageResult, InstantiateReturnValue,
	StorageDeposit,
};
use scale_info::TypeInfo;
use sp_core::{crypto::UncheckedFrom, Bytes};
use sp_runtime::traits::{Convert, Hash, Saturating, StaticLookup};
use sp_std::{fmt::Debug, prelude::*};

type CodeHash<T> = <T as frame_system::Config>::Hash;
type TrieId = Vec<u8>;
type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

/// The current storage version.
const STORAGE_VERSION: StorageVersion = StorageVersion::new(6);

/// Provides the contract address generation method.
///
/// See [`DefaultAddressGenerator`] for the default implementation.
pub trait AddressGenerator<T: frame_system::Config> {
	/// Generate the address of a contract based on the given instantiate parameters.
	///
	/// # Note for implementors
	/// 1. Make sure that there are no collisions, different inputs never lead to the same output.
	/// 2. Make sure that the same inputs lead to the same output.
	/// 3. Changing the implementation through a runtime upgrade without a proper storage migration
	/// would lead to catastrophic misbehavior.
	fn generate_address(
		deploying_address: &T::AccountId,
		code_hash: &CodeHash<T>,
		salt: &[u8],
	) -> T::AccountId;
}

/// Default address generator.
///
/// This is the default address generator used by contract instantiation. Its result
/// is only dependend on its inputs. It can therefore be used to reliably predict the
/// address of a contract. This is akin to the formular of eth's CREATE2 opcode. There
/// is no CREATE equivalent because CREATE2 is strictly more powerful.
///
/// Formula: `hash(deploying_address ++ code_hash ++ salt)`
pub struct DefaultAddressGenerator;

impl<T> AddressGenerator<T> for DefaultAddressGenerator
where
	T: frame_system::Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	fn generate_address(
		deploying_address: &T::AccountId,
		code_hash: &CodeHash<T>,
		salt: &[u8],
	) -> T::AccountId {
		let buf: Vec<_> = deploying_address
			.as_ref()
			.iter()
			.chain(code_hash.as_ref())
			.chain(salt)
			.cloned()
			.collect();
		UncheckedFrom::unchecked_from(T::Hashing::hash(&buf))
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The time implementation used to supply timestamps to conntracts through `seal_now`.
		type Time: Time;

		/// The generator used to supply randomness to contracts through `seal_random`.
		type Randomness: Randomness<Self::Hash, Self::BlockNumber>;

		/// The currency in which fees are paid and contract balances are held.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The overarching call type.
		type Call: Dispatchable<Origin = Self::Origin, PostInfo = PostDispatchInfo>
			+ GetDispatchInfo
			+ codec::Decode
			+ IsType<<Self as frame_system::Config>::Call>;

		/// Filter that is applied to calls dispatched by contracts.
		///
		/// Use this filter to control which dispatchables are callable by contracts.
		/// This is applied in **addition** to [`frame_system::Config::BaseCallFilter`].
		/// It is recommended to treat this as a whitelist.
		///
		/// # Stability
		///
		/// The runtime **must** make sure that all dispatchables that are callable by
		/// contracts remain stable. In addition [`Self::Call`] itself must remain stable.
		/// This means that no existing variants are allowed to switch their positions.
		///
		/// # Note
		///
		/// Note that dispatchables that are called via contracts do not spawn their
		/// own wasm instance for each call (as opposed to when called via a transaction).
		/// Therefore please make sure to be restrictive about which dispatchables are allowed
		/// in order to not introduce a new DoS vector like memory allocation patterns that can
		/// be exploited to drive the runtime into a panic.
		type CallFilter: Contains<<Self as frame_system::Config>::Call>;

		/// Used to answer contracts' queries regarding the current weight price. This is **not**
		/// used to calculate the actual fee and is only for informational purposes.
		type WeightPrice: Convert<Weight, BalanceOf<Self>>;

		/// Describes the weights of the dispatchables of this module and is also used to
		/// construct a default cost schedule.
		type WeightInfo: WeightInfo;

		/// Type that allows the runtime authors to add new host functions for a contract to call.
		type ChainExtension: chain_extension::ChainExtension<Self>;

		/// Cost schedule and limits.
		#[pallet::constant]
		type Schedule: Get<Schedule<Self>>;

		/// The type of the call stack determines the maximum nesting depth of contract calls.
		///
		/// The allowed depth is `CallStack::size() + 1`.
		/// Therefore a size of `0` means that a contract cannot use call or instantiate.
		/// In other words only the origin called "root contract" is allowed to execute then.
		type CallStack: smallvec::Array<Item = Frame<Self>>;

		/// The maximum number of tries that can be queued for deletion.
		#[pallet::constant]
		type DeletionQueueDepth: Get<u32>;

		/// The maximum amount of weight that can be consumed per block for lazy trie removal.
		#[pallet::constant]
		type DeletionWeightLimit: Get<Weight>;

		/// The amount of balance a caller has to pay for each byte of storage.
		///
		/// # Note
		///
		/// Changing this value for an existing chain might need a storage migration.
		#[pallet::constant]
		type DepositPerByte: Get<BalanceOf<Self>>;

		/// The amount of balance a caller has to pay for each storage item.
		/// # Note
		///
		/// Changing this value for an existing chain might need a storage migration.
		#[pallet::constant]
		type DepositPerItem: Get<BalanceOf<Self>>;

		/// The address generator used to generate the addresses of contracts.
		type AddressGenerator: AddressGenerator<Self>;
	}

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T>
	where
		T::AccountId: UncheckedFrom<T::Hash>,
		T::AccountId: AsRef<[u8]>,
	{
		fn on_initialize(_block: T::BlockNumber) -> Weight {
			// We do not want to go above the block limit and rather avoid lazy deletion
			// in that case. This should only happen on runtime upgrades.
			let weight_limit = T::BlockWeights::get()
				.max_block
				.saturating_sub(System::<T>::block_weight().total())
				.min(T::DeletionWeightLimit::get());
			Storage::<T>::process_deletion_queue_batch(weight_limit)
				.saturating_add(T::WeightInfo::on_initialize())
		}

		fn on_runtime_upgrade() -> Weight {
			migration::migrate::<T>()
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		T::AccountId: UncheckedFrom<T::Hash>,
		T::AccountId: AsRef<[u8]>,
		<BalanceOf<T> as HasCompact>::Type: Clone + Eq + PartialEq + Debug + TypeInfo + Encode,
	{
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
		#[pallet::weight(T::WeightInfo::call().saturating_add(*gas_limit))]
		pub fn call(
			origin: OriginFor<T>,
			dest: <T::Lookup as StaticLookup>::Source,
			#[pallet::compact] value: BalanceOf<T>,
			#[pallet::compact] gas_limit: Weight,
			storage_deposit_limit: Option<<BalanceOf<T> as codec::HasCompact>::Type>,
			data: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;
			let mut output = Self::internal_call(
				origin,
				dest,
				value,
				gas_limit,
				storage_deposit_limit.map(Into::into),
				data,
				None,
			);
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
		#[pallet::weight(
			T::WeightInfo::instantiate_with_code(
				code.len() as u32 / 1024,
				salt.len() as u32 / 1024,
			)
			.saturating_add(*gas_limit)
		)]
		pub fn instantiate_with_code(
			origin: OriginFor<T>,
			#[pallet::compact] value: BalanceOf<T>,
			#[pallet::compact] gas_limit: Weight,
			storage_deposit_limit: Option<<BalanceOf<T> as codec::HasCompact>::Type>,
			code: Vec<u8>,
			data: Vec<u8>,
			salt: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;
			let code_len = code.len() as u32;
			let salt_len = salt.len() as u32;
			let mut output = Self::internal_instantiate(
				origin,
				value,
				gas_limit,
				storage_deposit_limit.map(Into::into),
				Code::Upload(Bytes(code)),
				data,
				salt,
				None,
			);
			if let Ok(retval) = &output.result {
				if retval.1.did_revert() {
					output.result = Err(<Error<T>>::ContractReverted.into());
				}
			}
			output.gas_meter.into_dispatch_result(
				output.result.map(|(_address, result)| result),
				T::WeightInfo::instantiate_with_code(code_len / 1024, salt_len / 1024),
			)
		}

		/// Instantiates a contract from a previously deployed wasm binary.
		///
		/// This function is identical to [`Self::instantiate_with_code`] but without the
		/// code deployment step. Instead, the `code_hash` of an on-chain deployed wasm binary
		/// must be supplied.
		#[pallet::weight(
			T::WeightInfo::instantiate(salt.len() as u32 / 1024).saturating_add(*gas_limit)
		)]
		pub fn instantiate(
			origin: OriginFor<T>,
			#[pallet::compact] value: BalanceOf<T>,
			#[pallet::compact] gas_limit: Weight,
			storage_deposit_limit: Option<<BalanceOf<T> as codec::HasCompact>::Type>,
			code_hash: CodeHash<T>,
			data: Vec<u8>,
			salt: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;
			let salt_len = salt.len() as u32;
			let mut output = Self::internal_instantiate(
				origin,
				value,
				gas_limit,
				storage_deposit_limit.map(Into::into),
				Code::Existing(code_hash),
				data,
				salt,
				None,
			);
			if let Ok(retval) = &output.result {
				if retval.1.did_revert() {
					output.result = Err(<Error<T>>::ContractReverted.into());
				}
			}
			output.gas_meter.into_dispatch_result(
				output.result.map(|(_address, output)| output),
				T::WeightInfo::instantiate(salt_len / 1024),
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
		/// # Note
		///
		/// Anyone can instantiate a contract from any uploaded code and thus prevent its removal.
		/// To avoid this situation a constructor could employ access control so that it can
		/// only be instantiated by permissioned entities. The same is true when uploading
		/// through [`Self::instantiate_with_code`].
		#[pallet::weight(T::WeightInfo::upload_code(code.len() as u32 / 1024))]
		pub fn upload_code(
			origin: OriginFor<T>,
			code: Vec<u8>,
			storage_deposit_limit: Option<<BalanceOf<T> as codec::HasCompact>::Type>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;
			Self::bare_upload_code(origin, code, storage_deposit_limit.map(Into::into)).map(|_| ())
		}

		/// Remove the code stored under `code_hash` and refund the deposit to its owner.
		///
		/// A code can only be removed by its original uploader (its owner) and only if it is
		/// not used by any contract.
		#[pallet::weight(T::WeightInfo::remove_code())]
		pub fn remove_code(
			origin: OriginFor<T>,
			code_hash: CodeHash<T>,
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;
			<PrefabWasmModule<T>>::remove(&origin, code_hash)?;
			// we waive the fee because removing unused code is beneficial
			Ok(Pays::No.into())
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
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
	}

	#[pallet::error]
	pub enum Error<T> {
		/// A new schedule must have a greater version than the current one.
		InvalidScheduleVersion,
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
		/// The topics passed to `seal_deposit_events` contains at least one duplicate.
		DuplicateTopics,
		/// The chain does not provide a chain extension. Calling the chain extension results
		/// in this error. Note that this usually  shouldn't happen as deploying such contracts
		/// is rejected.
		NoChainExtension,
		/// Removal of a contract failed because the deletion queue is full.
		///
		/// This can happen when calling `seal_terminate`.
		/// The queue is filled by deleting contracts and emptied by a fixed amount each block.
		/// Trying again during another block is the only way to resolve this issue.
		DeletionQueueFull,
		/// A contract with the same AccountId already exists.
		DuplicateContract,
		/// A contract self destructed in its constructor.
		///
		/// This can be triggered by a call to `seal_terminate`.
		TerminatedInConstructor,
		/// The debug message specified to `seal_debug_message` does contain invalid UTF-8.
		DebugMessageInvalidUTF8,
		/// A call tried to invoke a contract that is flagged as non-reentrant.
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
	}

	/// A mapping from an original code hash to the original code, untouched by instrumentation.
	#[pallet::storage]
	pub(crate) type PristineCode<T: Config> = StorageMap<_, Identity, CodeHash<T>, Vec<u8>>;

	/// A mapping between an original code hash and instrumented wasm code, ready for execution.
	#[pallet::storage]
	pub(crate) type CodeStorage<T: Config> =
		StorageMap<_, Identity, CodeHash<T>, PrefabWasmModule<T>>;

	/// A mapping between an original code hash and its owner information.
	#[pallet::storage]
	pub(crate) type OwnerInfoOf<T: Config> = StorageMap<_, Identity, CodeHash<T>, OwnerInfo<T>>;

	/// The subtrie counter.
	#[pallet::storage]
	pub(crate) type AccountCounter<T: Config> = StorageValue<_, u64, ValueQuery>;

	/// The code associated with a given account.
	///
	/// TWOX-NOTE: SAFE since `AccountId` is a secure hash.
	#[pallet::storage]
	pub(crate) type ContractInfoOf<T: Config> =
		StorageMap<_, Twox64Concat, T::AccountId, ContractInfo<T>>;

	/// Evicted contracts that await child trie deletion.
	///
	/// Child trie deletion is a heavy operation depending on the amount of storage items
	/// stored in said trie. Therefore this operation is performed lazily in `on_initialize`.
	#[pallet::storage]
	pub(crate) type DeletionQueue<T: Config> = StorageValue<_, Vec<DeletedContract>, ValueQuery>;
}

/// Return type of the private [`Pallet::internal_call`] function.
type InternalCallOutput<T> = InternalOutput<T, ExecReturnValue>;

/// Return type of the private [`Pallet::internal_instantiate`] function.
type InternalInstantiateOutput<T> = InternalOutput<T, (AccountIdOf<T>, ExecReturnValue)>;

/// Return type of private helper functions.
struct InternalOutput<T: Config, O> {
	/// The gas meter that was used to execute the call.
	gas_meter: GasMeter<T>,
	/// The storage deposit used by the call.
	storage_deposit: StorageDeposit<BalanceOf<T>>,
	/// The result of the call.
	result: Result<O, ExecError>,
}

impl<T: Config> Pallet<T>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	/// Perform a call to a specified contract.
	///
	/// This function is similar to [`Self::call`], but doesn't perform any address lookups
	/// and better suitable for calling directly from Rust.
	///
	/// # Note
	///
	/// `debug` should only ever be set to `true` when executing as an RPC because
	/// it adds allocations and could be abused to drive the runtime into an OOM panic.
	/// If set to `true` it returns additional human readable debugging information.
	///
	/// It returns the execution result and the amount of used weight.
	pub fn bare_call(
		origin: T::AccountId,
		dest: T::AccountId,
		value: BalanceOf<T>,
		gas_limit: Weight,
		storage_deposit_limit: Option<BalanceOf<T>>,
		data: Vec<u8>,
		debug: bool,
	) -> ContractExecResult<BalanceOf<T>> {
		let mut debug_message = if debug { Some(Vec::new()) } else { None };
		let output = Self::internal_call(
			origin,
			dest,
			value,
			gas_limit,
			storage_deposit_limit,
			data,
			debug_message.as_mut(),
		);
		ContractExecResult {
			result: output.result.map_err(|r| r.error),
			gas_consumed: output.gas_meter.gas_consumed(),
			gas_required: output.gas_meter.gas_required(),
			storage_deposit: output.storage_deposit,
			debug_message: debug_message.unwrap_or_default(),
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
	/// `debug` should only ever be set to `true` when executing as an RPC because
	/// it adds allocations and could be abused to drive the runtime into an OOM panic.
	/// If set to `true` it returns additional human readable debugging information.
	pub fn bare_instantiate(
		origin: T::AccountId,
		value: BalanceOf<T>,
		gas_limit: Weight,
		storage_deposit_limit: Option<BalanceOf<T>>,
		code: Code<CodeHash<T>>,
		data: Vec<u8>,
		salt: Vec<u8>,
		debug: bool,
	) -> ContractInstantiateResult<T::AccountId, BalanceOf<T>> {
		let mut debug_message = if debug { Some(Vec::new()) } else { None };
		let output = Self::internal_instantiate(
			origin,
			value,
			gas_limit,
			storage_deposit_limit,
			code,
			data,
			salt,
			debug_message.as_mut(),
		);
		ContractInstantiateResult {
			result: output
				.result
				.map(|(account_id, result)| InstantiateReturnValue { result, account_id })
				.map_err(|e| e.error),
			gas_consumed: output.gas_meter.gas_consumed(),
			gas_required: output.gas_meter.gas_required(),
			storage_deposit: output.storage_deposit,
			debug_message: debug_message.unwrap_or_default(),
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
	) -> CodeUploadResult<CodeHash<T>, BalanceOf<T>> {
		let schedule = T::Schedule::get();
		let module = PrefabWasmModule::from_code(code, &schedule, origin)?;
		let deposit = module.open_deposit();
		if let Some(storage_deposit_limit) = storage_deposit_limit {
			ensure!(storage_deposit_limit >= deposit, <Error<T>>::StorageDepositLimitExhausted);
		}
		let result = CodeUploadReturnValue { code_hash: *module.code_hash(), deposit };
		module.store()?;
		Ok(result)
	}

	/// Query storage of a specified contract under a specified key.
	pub fn get_storage(address: T::AccountId, key: [u8; 32]) -> GetStorageResult {
		let contract_info =
			ContractInfoOf::<T>::get(&address).ok_or(ContractAccessError::DoesntExist)?;

		let maybe_value = Storage::<T>::read(&contract_info.trie_id, &key);
		Ok(maybe_value)
	}

	/// Determine the address of a contract.
	///
	/// This is the address generation function used by contract instantiation. See
	/// [`DefaultAddressGenerator`] for the default implementation.
	pub fn contract_address(
		deploying_address: &T::AccountId,
		code_hash: &CodeHash<T>,
		salt: &[u8],
	) -> T::AccountId {
		T::AddressGenerator::generate_address(deploying_address, code_hash, salt)
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
		self::wasm::reinstrument(module, schedule)
	}

	/// Internal function that does the actual call.
	///
	/// Called by dispatchables and public functions.
	fn internal_call(
		origin: T::AccountId,
		dest: T::AccountId,
		value: BalanceOf<T>,
		gas_limit: Weight,
		storage_deposit_limit: Option<BalanceOf<T>>,
		data: Vec<u8>,
		debug_message: Option<&mut Vec<u8>>,
	) -> InternalCallOutput<T> {
		let mut gas_meter = GasMeter::new(gas_limit);
		let mut storage_meter = match StorageMeter::new(&origin, storage_deposit_limit, value) {
			Ok(meter) => meter,
			Err(err) =>
				return InternalCallOutput {
					result: Err(err.into()),
					gas_meter,
					storage_deposit: Default::default(),
				},
		};
		let schedule = T::Schedule::get();
		let result = ExecStack::<T, PrefabWasmModule<T>>::run_call(
			origin,
			dest,
			&mut gas_meter,
			&mut storage_meter,
			&schedule,
			value,
			data,
			debug_message,
		);
		InternalCallOutput { result, gas_meter, storage_deposit: storage_meter.into_deposit() }
	}

	/// Internal function that does the actual instantiation.
	///
	/// Called by dispatchables and public functions.
	fn internal_instantiate(
		origin: T::AccountId,
		value: BalanceOf<T>,
		gas_limit: Weight,
		storage_deposit_limit: Option<BalanceOf<T>>,
		code: Code<CodeHash<T>>,
		data: Vec<u8>,
		salt: Vec<u8>,
		debug_message: Option<&mut Vec<u8>>,
	) -> InternalInstantiateOutput<T> {
		let mut storage_deposit = Default::default();
		let mut gas_meter = GasMeter::new(gas_limit);
		let try_exec = || {
			let schedule = T::Schedule::get();
			let (extra_deposit, executable) = match code {
				Code::Upload(Bytes(binary)) => {
					ensure!(
						binary.len() as u32 <= schedule.limits.code_len,
						<Error<T>>::CodeTooLarge
					);
					let executable =
						PrefabWasmModule::from_code(binary, &schedule, origin.clone())?;
					ensure!(
						executable.code_len() <= schedule.limits.code_len,
						<Error<T>>::CodeTooLarge
					);
					// The open deposit will be charged during execution when the
					// uploaded module does not already exist. This deposit is not part of the
					// storage meter because it is not transfered to the contract but
					// reserved on the uploading account.
					(executable.open_deposit(), executable)
				},
				Code::Existing(hash) => (
					Default::default(),
					PrefabWasmModule::from_storage(hash, &schedule, &mut gas_meter)?,
				),
			};
			let mut storage_meter = StorageMeter::new(
				&origin,
				storage_deposit_limit,
				value.saturating_add(extra_deposit),
			)?;
			let result = ExecStack::<T, PrefabWasmModule<T>>::run_instantiate(
				origin,
				executable,
				&mut gas_meter,
				&mut storage_meter,
				&schedule,
				value,
				data,
				&salt,
				debug_message,
			);
			storage_deposit = storage_meter
				.into_deposit()
				.saturating_add(&StorageDeposit::Charge(extra_deposit));
			result
		};
		InternalInstantiateOutput { result: try_exec(), gas_meter, storage_deposit }
	}
}
