// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

//! # Contract Module
//!
//! The Contract module provides functionality for the runtime to deploy and execute WebAssembly smart-contracts.
//!
//! - [`contract::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//!
//! ## Overview
//!
//! This module extends accounts based on the `Currency` trait to have smart-contract functionality. It can
//! be used with other modules that implement accounts based on `Currency`. These "smart-contract accounts"
//! have the ability to instantiate smart-contracts and make calls to other contract and non-contract accounts.
//!
//! The smart-contract code is stored once in a `code_cache`, and later retrievable via its `code_hash`.
//! This means that multiple smart-contracts can be instantiated from the same `code_cache`, without replicating
//! the code each time.
//!
//! When a smart-contract is called, its associated code is retrieved via the code hash and gets executed.
//! This call can alter the storage entries of the smart-contract account, instantiate new smart-contracts,
//! or call other smart-contracts.
//!
//! Finally, when an account is reaped, its associated code and storage of the smart-contract account
//! will also be deleted.
//!
//! ### Gas
//!
//! Senders must specify a gas limit with every call, as all instructions invoked by the smart-contract require gas.
//! Unused gas is refunded after the call, regardless of the execution outcome.
//!
//! If the gas limit is reached, then all calls and state changes (including balance transfers) are only
//! reverted at the current call's contract level. For example, if contract A calls B and B runs out of gas mid-call,
//! then all of B's calls are reverted. Assuming correct error handling by contract A, A's other calls and state
//! changes still persist.
//!
//! ### Notable Scenarios
//!
//! Contract call failures are not always cascading. When failures occur in a sub-call, they do not "bubble up",
//! and the call will only revert at the specific contract level. For example, if contract A calls contract B, and B
//! fails, A can decide how to handle that failure, either proceeding or reverting A's changes.
//!
//! ## Interface
//!
//! ### Dispatchable functions
//!
//! * `put_code` - Stores the given binary Wasm code into the chain's storage and returns its `code_hash`.
//! * `instantiate` - Deploys a new contract from the given `code_hash`, optionally transferring some balance.
//! This instantiates a new smart contract account and calls its contract deploy handler to
//! initialize the contract.
//! * `call` - Makes a call to an account, optionally transferring some balance.
//!
//! ## Usage
//!
//! The Contract module is a work in progress. The following examples show how this Contract module
//! can be used to instantiate and call contracts.
//!
//! * [`ink`](https://github.com/paritytech/ink) is
//! an [`eDSL`](https://wiki.haskell.org/Embedded_domain_specific_language) that enables writing
//! WebAssembly based smart contracts in the Rust programming language. This is a work in progress.
//!
//! ## Related Modules
//!
//! * [Balances](../pallet_balances/index.html)

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "runtime-benchmarks", recursion_limit="256")]

#[macro_use]
mod gas;
mod storage;
mod exec;
mod wasm;
mod rent;
mod benchmarking;
mod schedule;
mod weight_info;

#[cfg(test)]
mod tests;

use crate::exec::ExecutionContext;
use crate::wasm::{WasmLoader, WasmVm};

pub use crate::gas::{Gas, GasMeter};
pub use crate::wasm::ReturnCode as RuntimeReturnCode;
pub use crate::weight_info::WeightInfo;
pub use crate::schedule::{Schedule, HostFnWeights, InstructionWeights};

use sp_core::crypto::UncheckedFrom;
use sp_std::{prelude::*, marker::PhantomData, fmt::Debug};
use codec::{Codec, Encode, Decode};
use sp_runtime::{
	traits::{
		Hash, StaticLookup, Zero, MaybeSerializeDeserialize, Member, Convert, Saturating,
	},
	RuntimeDebug,
};
use frame_support::{
	decl_module, decl_event, decl_storage, decl_error, ensure,
	parameter_types, storage::child::ChildInfo,
	dispatch::{DispatchResult, DispatchResultWithPostInfo},
	traits::{OnUnbalanced, Currency, Get, Time, Randomness},
};
use frame_system::{ensure_signed, ensure_root};
use pallet_contracts_primitives::{
	RentProjectionResult, GetStorageResult, ContractAccessError, ContractExecResult, ExecResult,
};
use frame_support::weights::Weight;

pub type CodeHash<T> = <T as frame_system::Trait>::Hash;
pub type TrieId = Vec<u8>;

/// A function that generates an `AccountId` for a contract upon instantiation.
pub trait ContractAddressFor<CodeHash, AccountId> {
	fn contract_address_for(code_hash: &CodeHash, data: &[u8], origin: &AccountId) -> AccountId;
}

/// Information for managing an account and its sub trie abstraction.
/// This is the required info to cache for an account
#[derive(Encode, Decode, RuntimeDebug)]
pub enum ContractInfo<T: Trait> {
	Alive(AliveContractInfo<T>),
	Tombstone(TombstoneContractInfo<T>),
}

impl<T: Trait> ContractInfo<T> {
	/// If contract is alive then return some alive info
	pub fn get_alive(self) -> Option<AliveContractInfo<T>> {
		if let ContractInfo::Alive(alive) = self {
			Some(alive)
		} else {
			None
		}
	}
	/// If contract is alive then return some reference to alive info
	pub fn as_alive(&self) -> Option<&AliveContractInfo<T>> {
		if let ContractInfo::Alive(ref alive) = self {
			Some(alive)
		} else {
			None
		}
	}
	/// If contract is alive then return some mutable reference to alive info
	pub fn as_alive_mut(&mut self) -> Option<&mut AliveContractInfo<T>> {
		if let ContractInfo::Alive(ref mut alive) = self {
			Some(alive)
		} else {
			None
		}
	}

	/// If contract is tombstone then return some tombstone info
	pub fn get_tombstone(self) -> Option<TombstoneContractInfo<T>> {
		if let ContractInfo::Tombstone(tombstone) = self {
			Some(tombstone)
		} else {
			None
		}
	}
	/// If contract is tombstone then return some reference to tombstone info
	pub fn as_tombstone(&self) -> Option<&TombstoneContractInfo<T>> {
		if let ContractInfo::Tombstone(ref tombstone) = self {
			Some(tombstone)
		} else {
			None
		}
	}
	/// If contract is tombstone then return some mutable reference to tombstone info
	pub fn as_tombstone_mut(&mut self) -> Option<&mut TombstoneContractInfo<T>> {
		if let ContractInfo::Tombstone(ref mut tombstone) = self {
			Some(tombstone)
		} else {
			None
		}
	}
}

pub type AliveContractInfo<T> =
	RawAliveContractInfo<CodeHash<T>, BalanceOf<T>, <T as frame_system::Trait>::BlockNumber>;

/// Information for managing an account and its sub trie abstraction.
/// This is the required info to cache for an account.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct RawAliveContractInfo<CodeHash, Balance, BlockNumber> {
	/// Unique ID for the subtree encoded as a bytes vector.
	pub trie_id: TrieId,
	/// The total number of bytes used by this contract.
	///
	/// It is a sum of each key-value pair stored by this contract.
	pub storage_size: u32,
	/// The number of key-value pairs that have values of zero length.
	/// The condition `empty_pair_count ≤ total_pair_count` always holds.
	pub empty_pair_count: u32,
	/// The total number of key-value pairs in storage of this contract.
	pub total_pair_count: u32,
	/// The code associated with a given account.
	pub code_hash: CodeHash,
	/// Pay rent at most up to this value.
	pub rent_allowance: Balance,
	/// Last block rent has been payed.
	pub deduct_block: BlockNumber,
	/// Last block child storage has been written.
	pub last_write: Option<BlockNumber>,
}

impl<CodeHash, Balance, BlockNumber> RawAliveContractInfo<CodeHash, Balance, BlockNumber> {
	/// Associated child trie unique id is built from the hash part of the trie id.
	pub fn child_trie_info(&self) -> ChildInfo {
		child_trie_info(&self.trie_id[..])
	}
}

/// Associated child trie unique id is built from the hash part of the trie id.
pub(crate) fn child_trie_info(trie_id: &[u8]) -> ChildInfo {
	ChildInfo::new_default(trie_id)
}

pub type TombstoneContractInfo<T> =
	RawTombstoneContractInfo<<T as frame_system::Trait>::Hash, <T as frame_system::Trait>::Hashing>;

#[derive(Encode, Decode, PartialEq, Eq, RuntimeDebug)]
pub struct RawTombstoneContractInfo<H, Hasher>(H, PhantomData<Hasher>);

impl<H, Hasher> RawTombstoneContractInfo<H, Hasher>
where
	H: Member + MaybeSerializeDeserialize+ Debug
		+ AsRef<[u8]> + AsMut<[u8]> + Copy + Default
		+ sp_std::hash::Hash + Codec,
	Hasher: Hash<Output=H>,
{
	fn new(storage_root: &[u8], code_hash: H) -> Self {
		let mut buf = Vec::new();
		storage_root.using_encoded(|encoded| buf.extend_from_slice(encoded));
		buf.extend_from_slice(code_hash.as_ref());
		RawTombstoneContractInfo(<Hasher as Hash>::hash(&buf[..]), PhantomData)
	}
}

impl<T: Trait> From<AliveContractInfo<T>> for ContractInfo<T> {
	fn from(alive_info: AliveContractInfo<T>) -> Self {
		Self::Alive(alive_info)
	}
}

/// Get a trie id (trie id must be unique and collision resistant depending upon its context).
/// Note that it is different than encode because trie id should be collision resistant
/// (being a proper unique identifier).
pub trait TrieIdGenerator<AccountId> {
	/// Get a trie id for an account, using reference to parent account trie id to ensure
	/// uniqueness of trie id.
	///
	/// The implementation must ensure every new trie id is unique: two consecutive calls with the
	/// same parameter needs to return different trie id values.
	fn trie_id(account_id: &AccountId) -> TrieId;
}

/// Get trie id from `account_id`.
pub struct TrieIdFromParentCounter<T: Trait>(PhantomData<T>);

/// This generator uses inner counter for account id and applies the hash over `AccountId +
/// accountid_counter`.
impl<T: Trait> TrieIdGenerator<T::AccountId> for TrieIdFromParentCounter<T>
where
	T::AccountId: AsRef<[u8]>
{
	fn trie_id(account_id: &T::AccountId) -> TrieId {
		// Note that skipping a value due to error is not an issue here.
		// We only need uniqueness, not sequence.
		let new_seed = AccountCounter::mutate(|v| {
			*v = v.wrapping_add(1);
			*v
		});

		let mut buf = Vec::new();
		buf.extend_from_slice(account_id.as_ref());
		buf.extend_from_slice(&new_seed.to_le_bytes()[..]);
		T::Hashing::hash(&buf[..]).as_ref().into()
	}
}

pub type BalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
pub type NegativeImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;

parameter_types! {
	/// A reasonable default value for [`Trait::SignedClaimedHandicap`].
	pub const DefaultSignedClaimHandicap: u32 = 2;
	/// A reasonable default value for [`Trait::TombstoneDeposit`].
	pub const DefaultTombstoneDeposit: u32 = 16;
	/// A reasonable default value for [`Trait::StorageSizeOffset`].
	pub const DefaultStorageSizeOffset: u32 = 8;
	/// A reasonable default value for [`Trait::RentByteFee`].
	pub const DefaultRentByteFee: u32 = 4;
	/// A reasonable default value for [`Trait::RentDepositOffset`].
	pub const DefaultRentDepositOffset: u32 = 1000;
	/// A reasonable default value for [`Trait::SurchargeReward`].
	pub const DefaultSurchargeReward: u32 = 150;
	/// A reasonable default value for [`Trait::MaxDepth`].
	pub const DefaultMaxDepth: u32 = 32;
	/// A reasonable default value for [`Trait::MaxValueSize`].
	pub const DefaultMaxValueSize: u32 = 16_384;
}

pub trait Trait: frame_system::Trait {
	type Time: Time;
	type Randomness: Randomness<Self::Hash>;

	/// The currency in which fees are paid and contract balances are held.
	type Currency: Currency<Self::AccountId>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// A function type to get the contract address given the instantiator.
	type DetermineContractAddress: ContractAddressFor<CodeHash<Self>, Self::AccountId>;

	/// trie id generator
	type TrieIdGenerator: TrieIdGenerator<Self::AccountId>;

	/// Handler for rent payments.
	type RentPayment: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Number of block delay an extrinsic claim surcharge has.
	///
	/// When claim surcharge is called by an extrinsic the rent is checked
	/// for current_block - delay
	type SignedClaimHandicap: Get<Self::BlockNumber>;

	/// The minimum amount required to generate a tombstone.
	type TombstoneDeposit: Get<BalanceOf<Self>>;

	/// A size offset for an contract. A just created account with untouched storage will have that
	/// much of storage from the perspective of the state rent.
	///
	/// This is a simple way to ensure that contracts with empty storage eventually get deleted by
	/// making them pay rent. This creates an incentive to remove them early in order to save rent.
	type StorageSizeOffset: Get<u32>;

	/// Price of a byte of storage per one block interval. Should be greater than 0.
	type RentByteFee: Get<BalanceOf<Self>>;

	/// The amount of funds a contract should deposit in order to offset
	/// the cost of one byte.
	///
	/// Let's suppose the deposit is 1,000 BU (balance units)/byte and the rent is 1 BU/byte/day,
	/// then a contract with 1,000,000 BU that uses 1,000 bytes of storage would pay no rent.
	/// But if the balance reduced to 500,000 BU and the storage stayed the same at 1,000,
	/// then it would pay 500 BU/day.
	type RentDepositOffset: Get<BalanceOf<Self>>;

	/// Reward that is received by the party whose touch has led
	/// to removal of a contract.
	type SurchargeReward: Get<BalanceOf<Self>>;

	/// The maximum nesting level of a call/instantiate stack.
	type MaxDepth: Get<u32>;

	/// The maximum size of a storage value and event payload in bytes.
	type MaxValueSize: Get<u32>;

	/// Used to answer contracts's queries regarding the current weight price. This is **not**
	/// used to calculate the actual fee and is only for informational purposes.
	type WeightPrice: Convert<Weight, BalanceOf<Self>>;

	/// Describes the weights of the dispatchables of this module and is also used to
	/// construct a default cost schedule.
	type WeightInfo: WeightInfo;
}

/// Simple contract address determiner.
///
/// Address calculated from the code (of the constructor), input data to the constructor,
/// and the account id that requested the account creation.
///
/// Formula: `blake2_256(blake2_256(code) + blake2_256(data) + origin)`
pub struct SimpleAddressDeterminer<T: Trait>(PhantomData<T>);
impl<T: Trait> ContractAddressFor<CodeHash<T>, T::AccountId> for SimpleAddressDeterminer<T>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>
{
	fn contract_address_for(code_hash: &CodeHash<T>, data: &[u8], origin: &T::AccountId) -> T::AccountId {
		let data_hash = T::Hashing::hash(data);

		let mut buf = Vec::new();
		buf.extend_from_slice(code_hash.as_ref());
		buf.extend_from_slice(data_hash.as_ref());
		buf.extend_from_slice(origin.as_ref());

		UncheckedFrom::unchecked_from(T::Hashing::hash(&buf[..]))
	}
}

decl_error! {
	/// Error for the contracts module.
	pub enum Error for Module<T: Trait> {
		/// A new schedule must have a greater version than the current one.
		InvalidScheduleVersion,
		/// An origin must be signed or inherent and auxiliary sender only provided on inherent.
		InvalidSurchargeClaim,
		/// Cannot restore from nonexisting or tombstone contract.
		InvalidSourceContract,
		/// Cannot restore to nonexisting or alive contract.
		InvalidDestinationContract,
		/// Tombstones don't match.
		InvalidTombstone,
		/// An origin TrieId written in the current block.
		InvalidContractOrigin,
		/// The executed contract exhausted its gas limit.
		OutOfGas,
		/// The output buffer supplied to a contract API call was too small.
		OutputBufferTooSmall,
		/// Performing the requested transfer would have brought the contract below
		/// the subsistence threshold. No transfer is allowed to do this in order to allow
		/// for a tombstone to be created. Use `seal_terminate` to remove a contract without
		/// leaving a tombstone behind.
		BelowSubsistenceThreshold,
		/// The newly created contract is below the subsistence threshold after executing
		/// its contructor. No contracts are allowed to exist below that threshold.
		NewContractNotFunded,
		/// Performing the requested transfer failed for a reason originating in the
		/// chosen currency implementation of the runtime. Most probably the balance is
		/// too low or locks are placed on it.
		TransferFailed,
		/// Performing a call was denied because the calling depth reached the limit
		/// of what is specified in the schedule.
		MaxCallDepthReached,
		/// The contract that was called is either no contract at all (a plain account)
		/// or is a tombstone.
		NotCallable,
		/// The code supplied to `put_code` exceeds the limit specified in the current schedule.
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
	}
}

decl_module! {
	/// Contracts module.
	pub struct Module<T: Trait> for enum Call where origin: <T as frame_system::Trait>::Origin {
		type Error = Error<T>;

		/// Number of block delay an extrinsic claim surcharge has.
		///
		/// When claim surcharge is called by an extrinsic the rent is checked
		/// for current_block - delay
		const SignedClaimHandicap: T::BlockNumber = T::SignedClaimHandicap::get();

		/// The minimum amount required to generate a tombstone.
		const TombstoneDeposit: BalanceOf<T> = T::TombstoneDeposit::get();

		/// A size offset for an contract. A just created account with untouched storage will have that
		/// much of storage from the perspective of the state rent.
		///
		/// This is a simple way to ensure that contracts with empty storage eventually get deleted
		/// by making them pay rent. This creates an incentive to remove them early in order to save
		/// rent.
		const StorageSizeOffset: u32 = T::StorageSizeOffset::get();

		/// Price of a byte of storage per one block interval. Should be greater than 0.
		const RentByteFee: BalanceOf<T> = T::RentByteFee::get();

		/// The amount of funds a contract should deposit in order to offset
		/// the cost of one byte.
		///
		/// Let's suppose the deposit is 1,000 BU (balance units)/byte and the rent is 1 BU/byte/day,
		/// then a contract with 1,000,000 BU that uses 1,000 bytes of storage would pay no rent.
		/// But if the balance reduced to 500,000 BU and the storage stayed the same at 1,000,
		/// then it would pay 500 BU/day.
		const RentDepositOffset: BalanceOf<T> = T::RentDepositOffset::get();

		/// Reward that is received by the party whose touch has led
		/// to removal of a contract.
		const SurchargeReward: BalanceOf<T> = T::SurchargeReward::get();

		/// The maximum nesting level of a call/instantiate stack. A reasonable default
		/// value is 100.
		const MaxDepth: u32 = T::MaxDepth::get();

		/// The maximum size of a storage value in bytes. A reasonable default is 16 KiB.
		const MaxValueSize: u32 = T::MaxValueSize::get();

		fn deposit_event() = default;

		/// Updates the schedule for metering contracts.
		///
		/// The schedule must have a greater version than the stored schedule.
		#[weight = T::WeightInfo::update_schedule()]
		pub fn update_schedule(origin, schedule: Schedule<T>) -> DispatchResult {
			ensure_root(origin)?;
			if <Module<T>>::current_schedule().version >= schedule.version {
				Err(Error::<T>::InvalidScheduleVersion)?
			}

			Self::deposit_event(RawEvent::ScheduleUpdated(schedule.version));
			CurrentSchedule::put(schedule);

			Ok(())
		}

		/// Stores the given binary Wasm code into the chain's storage and returns its `codehash`.
		/// You can instantiate contracts only with stored code.
		#[weight = T::WeightInfo::put_code(code.len() as u32 / 1024)]
		pub fn put_code(
			origin,
			code: Vec<u8>
		) -> DispatchResult {
			ensure_signed(origin)?;
			let schedule = <Module<T>>::current_schedule();
			ensure!(code.len() as u32 <= schedule.max_code_size, Error::<T>::CodeTooLarge);
			let result = wasm::save_code::<T>(code, &schedule);
			if let Ok(code_hash) = result {
				Self::deposit_event(RawEvent::CodeStored(code_hash));
			}
			result.map(|_| ()).map_err(Into::into)
		}

		/// Makes a call to an account, optionally transferring some balance.
		///
		/// * If the account is a smart-contract account, the associated code will be
		/// executed and any value will be transferred.
		/// * If the account is a regular account, any value will be transferred.
		/// * If no account exists and the call value is not less than `existential_deposit`,
		/// a regular account will be created and any value will be transferred.
		#[weight = T::WeightInfo::call().saturating_add(*gas_limit)]
		pub fn call(
			origin,
			dest: <T::Lookup as StaticLookup>::Source,
			#[compact] value: BalanceOf<T>,
			#[compact] gas_limit: Gas,
			data: Vec<u8>
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;
			let mut gas_meter = GasMeter::new(gas_limit);

			let result = Self::execute_wasm(origin, &mut gas_meter, |ctx, gas_meter| {
				ctx.call(dest, value, gas_meter, data)
			});
			gas_meter.into_dispatch_result(result)
		}

		/// Instantiates a new contract from the `codehash` generated by `put_code`, optionally transferring some balance.
		///
		/// Instantiation is executed as follows:
		///
		/// - The destination address is computed based on the sender and hash of the code.
		/// - The smart-contract account is created at the computed address.
		/// - The `ctor_code` is executed in the context of the newly-created account. Buffer returned
		///   after the execution is saved as the `code` of the account. That code will be invoked
		///   upon any call received by this account.
		/// - The contract is initialized.
		#[weight = T::WeightInfo::instantiate(data.len() as u32 / 1024).saturating_add(*gas_limit)]
		pub fn instantiate(
			origin,
			#[compact] endowment: BalanceOf<T>,
			#[compact] gas_limit: Gas,
			code_hash: CodeHash<T>,
			data: Vec<u8>
		) -> DispatchResultWithPostInfo {
			let origin = ensure_signed(origin)?;
			let mut gas_meter = GasMeter::new(gas_limit);

			let result = Self::execute_wasm(origin, &mut gas_meter, |ctx, gas_meter| {
				ctx.instantiate(endowment, gas_meter, &code_hash, data)
					.map(|(_address, output)| output)
			});
			gas_meter.into_dispatch_result(result)
		}

		/// Allows block producers to claim a small reward for evicting a contract. If a block producer
		/// fails to do so, a regular users will be allowed to claim the reward.
		///
		/// If contract is not evicted as a result of this call, no actions are taken and
		/// the sender is not eligible for the reward.
		#[weight = T::WeightInfo::claim_surcharge()]
		fn claim_surcharge(origin, dest: T::AccountId, aux_sender: Option<T::AccountId>) {
			let origin = origin.into();
			let (signed, rewarded) = match (origin, aux_sender) {
				(Ok(frame_system::RawOrigin::Signed(account)), None) => {
					(true, account)
				},
				(Ok(frame_system::RawOrigin::None), Some(aux_sender)) => {
					(false, aux_sender)
				},
				_ => Err(Error::<T>::InvalidSurchargeClaim)?,
			};

			// Add some advantage for block producers (who send unsigned extrinsics) by
			// adding a handicap: for signed extrinsics we use a slightly older block number
			// for the eviction check. This can be viewed as if we pushed regular users back in past.
			let handicap = if signed {
				T::SignedClaimHandicap::get()
			} else {
				Zero::zero()
			};

			// If poking the contract has lead to eviction of the contract, give out the rewards.
			if rent::snitch_contract_should_be_evicted::<T>(&dest, handicap) {
				T::Currency::deposit_into_existing(&rewarded, T::SurchargeReward::get())?;
			}
		}
	}
}

/// Public APIs provided by the contracts module.
impl<T: Trait> Module<T> {
	/// Perform a call to a specified contract.
	///
	/// This function is similar to `Self::call`, but doesn't perform any address lookups and better
	/// suitable for calling directly from Rust.
	///
	/// It returns the exection result and the amount of used weight.
	pub fn bare_call(
		origin: T::AccountId,
		dest: T::AccountId,
		value: BalanceOf<T>,
		gas_limit: Gas,
		input_data: Vec<u8>,
	) -> ContractExecResult {
		let mut gas_meter = GasMeter::new(gas_limit);
		let exec_result = Self::execute_wasm(origin, &mut gas_meter, |ctx, gas_meter| {
			ctx.call(dest, value, gas_meter, input_data)
		});
		let gas_consumed = gas_meter.gas_spent();
		ContractExecResult {
			exec_result,
			gas_consumed,
		}
	}

	/// Query storage of a specified contract under a specified key.
	pub fn get_storage(address: T::AccountId, key: [u8; 32]) -> GetStorageResult {
		let contract_info = ContractInfoOf::<T>::get(&address)
			.ok_or(ContractAccessError::DoesntExist)?
			.get_alive()
			.ok_or(ContractAccessError::IsTombstone)?;

		let maybe_value = storage::read_contract_storage(&contract_info.trie_id, &key);
		Ok(maybe_value)
	}

	pub fn rent_projection(address: T::AccountId) -> RentProjectionResult<T::BlockNumber> {
		rent::compute_rent_projection::<T>(&address)
	}

	/// Put code for benchmarks which does not check or instrument the code.
	#[cfg(feature = "runtime-benchmarks")]
	pub fn put_code_raw(code: Vec<u8>) -> DispatchResult {
		let schedule = <Module<T>>::current_schedule();
		let result = wasm::save_code_raw::<T>(code, &schedule);
		result.map(|_| ()).map_err(Into::into)
	}
}

impl<T: Trait> Module<T> {
	fn execute_wasm(
		origin: T::AccountId,
		gas_meter: &mut GasMeter<T>,
		func: impl FnOnce(&mut ExecutionContext<T, WasmVm<T>, WasmLoader<T>>, &mut GasMeter<T>) -> ExecResult,
	) -> ExecResult {
		let cfg = Config::preload();
		let vm = WasmVm::new(&cfg.schedule);
		let loader = WasmLoader::new(&cfg.schedule);
		let mut ctx = ExecutionContext::top_level(origin, &cfg, &vm, &loader);
		func(&mut ctx, gas_meter)
	}
}

decl_event! {
	pub enum Event<T>
	where
		Balance = BalanceOf<T>,
		<T as frame_system::Trait>::AccountId,
		<T as frame_system::Trait>::Hash
	{
		/// Contract deployed by address at the specified address. \[owner, contract\]
		Instantiated(AccountId, AccountId),

		/// Contract has been evicted and is now in tombstone state.
		/// \[contract, tombstone\]
		///
		/// # Params
		///
		/// - `contract`: `AccountId`: The account ID of the evicted contract.
		/// - `tombstone`: `bool`: True if the evicted contract left behind a tombstone.
		Evicted(AccountId, bool),

		/// Restoration for a contract has been successful.
		/// \[donor, dest, code_hash, rent_allowance\]
		///
		/// # Params
		///
		/// - `donor`: `AccountId`: Account ID of the restoring contract
		/// - `dest`: `AccountId`: Account ID of the restored contract
		/// - `code_hash`: `Hash`: Code hash of the restored contract
		/// - `rent_allowance: `Balance`: Rent allowance of the restored contract
		Restored(AccountId, AccountId, Hash, Balance),

		/// Code with the specified hash has been stored.
		/// \[code_hash\]
		CodeStored(Hash),

		/// Triggered when the current \[schedule\] is updated.
		ScheduleUpdated(u32),

		/// An event deposited upon execution of a contract from the account.
		/// \[account, data\]
		ContractExecution(AccountId, Vec<u8>),
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Contracts {
		/// Current cost schedule for contracts.
		CurrentSchedule get(fn current_schedule) config(): Schedule<T> = Default::default();
		/// A mapping from an original code hash to the original code, untouched by instrumentation.
		pub PristineCode: map hasher(identity) CodeHash<T> => Option<Vec<u8>>;
		/// A mapping between an original code hash and instrumented wasm code, ready for execution.
		pub CodeStorage: map hasher(identity) CodeHash<T> => Option<wasm::PrefabWasmModule>;
		/// The subtrie counter.
		pub AccountCounter: u64 = 0;
		/// The code associated with a given account.
		///
		/// TWOX-NOTE: SAFE since `AccountId` is a secure hash.
		pub ContractInfoOf: map hasher(twox_64_concat) T::AccountId => Option<ContractInfo<T>>;
	}
}

/// In-memory cache of configuration values.
///
/// We assume that these values can't be changed in the
/// course of transaction execution.
pub struct Config<T: Trait> {
	pub schedule: Schedule<T>,
	pub existential_deposit: BalanceOf<T>,
	pub tombstone_deposit: BalanceOf<T>,
	pub max_depth: u32,
	pub max_value_size: u32,
}

impl<T: Trait> Config<T> {
	fn preload() -> Config<T> {
		Config {
			schedule: <Module<T>>::current_schedule(),
			existential_deposit: T::Currency::minimum_balance(),
			tombstone_deposit: T::TombstoneDeposit::get(),
			max_depth: T::MaxDepth::get(),
			max_value_size: T::MaxValueSize::get(),
		}
	}

	/// Subsistence threshold is the extension of the minimum balance (aka existential deposit) by the
	/// tombstone deposit, required for leaving a tombstone.
	///
	/// Rent or any contract initiated balance transfer mechanism cannot make the balance lower
	/// than the subsistence threshold in order to guarantee that a tombstone is created.
	///
	/// The only way to completely kill a contract without a tombstone is calling `seal_terminate`.
	pub fn subsistence_threshold(&self) -> BalanceOf<T> {
		self.existential_deposit.saturating_add(self.tombstone_deposit)
	}

	/// The same as `subsistence_threshold` but without the need for a preloaded instance.
	///
	/// This is for cases where this value is needed in rent calculation rather than
	/// during contract execution.
	pub fn subsistence_threshold_uncached() -> BalanceOf<T> {
		T::Currency::minimum_balance().saturating_add(T::TombstoneDeposit::get())
	}
}
