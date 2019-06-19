// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
//! have the ability to create smart-contracts and make calls to other contract and non-contract accounts.
//!
//! The smart-contract code is stored once in a `code_cache`, and later retrievable via its `code_hash`.
//! This means that multiple smart-contracts can be instantiated from the same `code_cache`, without replicating
//! the code each time.
//!
//! When a smart-contract is called, its associated code is retrieved via the code hash and gets executed.
//! This call can alter the storage entries of the smart-contract account, create new smart-contracts,
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
//! * `create` - Deploys a new contract from the given `code_hash`, optionally transferring some balance.
//! This creates a new smart contract account and calls its contract deploy handler to initialize the contract.
//! * `call` - Makes a call to an account, optionally transferring some balance.
//!
//! ## Usage
//!
//! The Contract module is a work in progress. The following examples show how this Contract module can be
//! used to create and call contracts.
//!
//! * [`pDSL`](https://github.com/Robbepop/pdsl) is a domain specific language that enables writing
//! WebAssembly based smart contracts in the Rust programming language. This is a work in progress.
//!
//! ## Related Modules
//!
//! * [Balances](../srml_balances/index.html)

#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
mod gas;

mod account_db;
mod exec;
mod wasm;
mod rent;

#[cfg(test)]
mod tests;

use crate::exec::ExecutionContext;
use crate::account_db::{AccountDb, DirectAccountDb};

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use substrate_primitives::crypto::UncheckedFrom;
use rstd::{prelude::*, marker::PhantomData, convert::TryFrom};
use parity_codec::{Codec, Encode, Decode};
use runtime_io::blake2_256;
use runtime_primitives::traits::{
	Hash, SimpleArithmetic, Bounded, StaticLookup, Zero, MaybeSerializeDebug, Member
};
use srml_support::dispatch::{Result, Dispatchable};
use srml_support::{
	Parameter, StorageMap, StorageValue, decl_module, decl_event, decl_storage, storage::child
};
use srml_support::traits::{OnFreeBalanceZero, OnUnbalanced, Currency};
use system::{ensure_signed, RawOrigin};
use substrate_primitives::storage::well_known_keys::CHILD_STORAGE_KEY_PREFIX;
use timestamp;

pub type CodeHash<T> = <T as system::Trait>::Hash;
pub type TrieId = Vec<u8>;

/// A function that generates an `AccountId` for a contract upon instantiation.
pub trait ContractAddressFor<CodeHash, AccountId> {
	fn contract_address_for(code_hash: &CodeHash, data: &[u8], origin: &AccountId) -> AccountId;
}

/// A function that returns the fee for dispatching a `Call`.
pub trait ComputeDispatchFee<Call, Balance> {
	fn compute_dispatch_fee(call: &Call) -> Balance;
}

/// Information for managing an acocunt and its sub trie abstraction.
/// This is the required info to cache for an account
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
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

	/// If contract is tombstone then return some alive info
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
	RawAliveContractInfo<CodeHash<T>, BalanceOf<T>, <T as system::Trait>::BlockNumber>;

/// Information for managing an account and its sub trie abstraction.
/// This is the required info to cache for an account.
// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct RawAliveContractInfo<CodeHash, Balance, BlockNumber> {
	/// Unique ID for the subtree encoded as a bytes vector.
	pub trie_id: TrieId,
	/// The size of stored value in octet.
	pub storage_size: u32,
	/// The code associated with a given account.
	pub code_hash: CodeHash,
	/// Pay rent at most up to this value.
	pub rent_allowance: Balance,
	/// Last block rent has been payed.
	pub deduct_block: BlockNumber,
	/// Last block child storage has been written.
	pub last_write: Option<BlockNumber>,
}

pub type TombstoneContractInfo<T> =
	RawTombstoneContractInfo<<T as system::Trait>::Hash, <T as system::Trait>::Hashing>;

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Encode, Decode, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct RawTombstoneContractInfo<H, Hasher>(H, PhantomData<Hasher>);

impl<H, Hasher> RawTombstoneContractInfo<H, Hasher>
where
	H: Member + MaybeSerializeDebug + AsRef<[u8]> + AsMut<[u8]> + Copy + Default + rstd::hash::Hash
		+ Codec,
	Hasher: Hash<Output=H>,
{
	fn new(storage_root: &[u8], code_hash: H) -> Self {
		let mut buf = Vec::new();
		storage_root.using_encoded(|encoded| buf.extend_from_slice(encoded));
		buf.extend_from_slice(code_hash.as_ref());
		RawTombstoneContractInfo(Hasher::hash(&buf[..]), PhantomData)
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
	///
	/// Also, the implementation is responsible for ensuring that `TrieId` starts with
	/// `:child_storage:`.
	/// TODO: We want to change this, see https://github.com/paritytech/substrate/issues/2325
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
		let new_seed = <AccountCounter<T>>::mutate(|v| {
			*v = v.wrapping_add(1);
			*v
		});

		let mut buf = Vec::new();
		buf.extend_from_slice(account_id.as_ref());
		buf.extend_from_slice(&new_seed.to_le_bytes()[..]);

		// TODO: see https://github.com/paritytech/substrate/issues/2325
		CHILD_STORAGE_KEY_PREFIX.iter()
			.chain(b"default:")
			.chain(T::Hashing::hash(&buf[..]).as_ref().iter())
			.cloned()
			.collect()
	}
}

pub type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
pub type NegativeImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;

pub trait Trait: timestamp::Trait {
	type Currency: Currency<Self::AccountId>;

	/// The outer call dispatch type.
	type Call: Parameter + Dispatchable<Origin=<Self as system::Trait>::Origin>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	type Gas: Parameter + Default + Codec + SimpleArithmetic + Bounded + Copy +
		Into<BalanceOf<Self>> + TryFrom<BalanceOf<Self>>;

	/// A function type to get the contract address given the creator.
	type DetermineContractAddress: ContractAddressFor<CodeHash<Self>, Self::AccountId>;

	/// A function type that computes the fee for dispatching the given `Call`.
	///
	/// It is recommended (though not required) for this function to return a fee that would be taken
	/// by the Executive module for regular dispatch.
	type ComputeDispatchFee: ComputeDispatchFee<Self::Call, BalanceOf<Self>>;

	/// trieid id generator
	type TrieIdGenerator: TrieIdGenerator<Self::AccountId>;

	/// Handler for the unbalanced reduction when making a gas payment.
	type GasPayment: OnUnbalanced<NegativeImbalanceOf<Self>>;
}

/// Simple contract address determiner.
///
/// Address calculated from the code (of the constructor), input data to the constructor,
/// and the account id that requested the account creation.
///
/// Formula: `blake2_256(blake2_256(code) + blake2_256(data) + origin)`
pub struct SimpleAddressDeterminator<T: Trait>(PhantomData<T>);
impl<T: Trait> ContractAddressFor<CodeHash<T>, T::AccountId> for SimpleAddressDeterminator<T>
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

/// The default dispatch fee computor computes the fee in the same way that
/// the implementation of `MakePayment` for the Balances module does.
pub struct DefaultDispatchFeeComputor<T: Trait>(PhantomData<T>);
impl<T: Trait> ComputeDispatchFee<T::Call, BalanceOf<T>> for DefaultDispatchFeeComputor<T> {
	fn compute_dispatch_fee(call: &T::Call) -> BalanceOf<T> {
		let encoded_len = call.using_encoded(|encoded| encoded.len() as u32);
		let base_fee = <Module<T>>::transaction_base_fee();
		let byte_fee = <Module<T>>::transaction_byte_fee();
		base_fee + byte_fee * encoded_len.into()
	}
}

decl_module! {
	/// Contracts module.
	pub struct Module<T: Trait> for enum Call where origin: <T as system::Trait>::Origin {
		fn deposit_event<T>() = default;

		/// Updates the schedule for metering contracts.
		///
		/// The schedule must have a greater version than the stored schedule.
		pub fn update_schedule(schedule: Schedule<T::Gas>) -> Result {
			if <Module<T>>::current_schedule().version >= schedule.version {
				return Err("new schedule must have a greater version than current");
			}

			Self::deposit_event(RawEvent::ScheduleUpdated(schedule.version));
			<CurrentSchedule<T>>::put(schedule);

			Ok(())
		}

		/// Stores the given binary Wasm code into the chain's storage and returns its `codehash`.
		/// You can instantiate contracts only with stored code.
		pub fn put_code(
			origin,
			#[compact] gas_limit: T::Gas,
			code: Vec<u8>
		) -> Result {
			let origin = ensure_signed(origin)?;
			let schedule = <Module<T>>::current_schedule();

			let (mut gas_meter, imbalance) = gas::buy_gas::<T>(&origin, gas_limit)?;

			let result = wasm::save_code::<T>(code, &mut gas_meter, &schedule);
			if let Ok(code_hash) = result {
				Self::deposit_event(RawEvent::CodeStored(code_hash));
			}

			gas::refund_unused_gas::<T>(&origin, gas_meter, imbalance);

			result.map(|_| ())
		}

		/// Makes a call to an account, optionally transferring some balance.
		///
		/// * If the account is a smart-contract account, the associated code will be
		/// executed and any value will be transferred.
		/// * If the account is a regular account, any value will be transferred.
		/// * If no account exists and the call value is not less than `existential_deposit`,
		/// a regular account will be created and any value will be transferred.
		pub fn call(
			origin,
			dest: <T::Lookup as StaticLookup>::Source,
			#[compact] value: BalanceOf<T>,
			#[compact] gas_limit: T::Gas,
			data: Vec<u8>
		) -> Result {
			let origin = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;

			// Pay for the gas upfront.
			//
			// NOTE: it is very important to avoid any state changes before
			// paying for the gas.
			let (mut gas_meter, imbalance) = gas::buy_gas::<T>(&origin, gas_limit)?;

			let cfg = Config::preload();
			let vm = crate::wasm::WasmVm::new(&cfg.schedule);
			let loader = crate::wasm::WasmLoader::new(&cfg.schedule);
			let mut ctx = ExecutionContext::top_level(origin.clone(), &cfg, &vm, &loader);

			let result = ctx.call(dest, value, &mut gas_meter, &data, exec::EmptyOutputBuf::new());

			if let Ok(_) = result {
				// Commit all changes that made it thus far into the persistent storage.
				DirectAccountDb.commit(ctx.overlay.into_change_set());

				// Then deposit all events produced.
				ctx.events.into_iter().for_each(|indexed_event| {
					<system::Module<T>>::deposit_event_indexed(
						&*indexed_event.topics,
						<T as Trait>::Event::from(indexed_event.event).into(),
					);
				});
			}

			// Refund cost of the unused gas.
			//
			// NOTE: This should go after the commit to the storage, since the storage changes
			// can alter the balance of the caller.
			gas::refund_unused_gas::<T>(&origin, gas_meter, imbalance);

			// Dispatch every recorded call with an appropriate origin.
			ctx.calls.into_iter().for_each(|(who, call)| {
				let result = call.dispatch(RawOrigin::Signed(who.clone()).into());
				Self::deposit_event(RawEvent::Dispatched(who, result.is_ok()));
			});

			result.map(|_| ())
		}

		/// Creates a new contract from the `codehash` generated by `put_code`, optionally transferring some balance.
		///
		/// Creation is executed as follows:
		///
		/// - The destination address is computed based on the sender and hash of the code.
		/// - The smart-contract account is created at the computed address.
		/// - The `ctor_code` is executed in the context of the newly-created account. Buffer returned
		///   after the execution is saved as the `code` of the account. That code will be invoked
		///   upon any call received by this account.
		/// - The contract is initialized.
		pub fn create(
			origin,
			#[compact] endowment: BalanceOf<T>,
			#[compact] gas_limit: T::Gas,
			code_hash: CodeHash<T>,
			data: Vec<u8>
		) -> Result {
			let origin = ensure_signed(origin)?;

			// Commit the gas upfront.
			//
			// NOTE: It is very important to avoid any state changes before
			// paying for the gas.
			let (mut gas_meter, imbalance) = gas::buy_gas::<T>(&origin, gas_limit)?;

			let cfg = Config::preload();
			let vm = crate::wasm::WasmVm::new(&cfg.schedule);
			let loader = crate::wasm::WasmLoader::new(&cfg.schedule);
			let mut ctx = ExecutionContext::top_level(origin.clone(), &cfg, &vm, &loader);
			let result = ctx.instantiate(endowment, &mut gas_meter, &code_hash, &data);

			if let Ok(_) = result {
				// Commit all changes that made it thus far into the persistent storage.
				DirectAccountDb.commit(ctx.overlay.into_change_set());

				// Then deposit all events produced.
				ctx.events.into_iter().for_each(|indexed_event| {
					<system::Module<T>>::deposit_event_indexed(
						&*indexed_event.topics,
						<T as Trait>::Event::from(indexed_event.event).into(),
					);
				});
			}

			// Refund cost of the unused gas.
			//
			// NOTE: This should go after the commit to the storage, since the storage changes
			// can alter the balance of the caller.
			gas::refund_unused_gas::<T>(&origin, gas_meter, imbalance);

			// Dispatch every recorded call with an appropriate origin.
			ctx.calls.into_iter().for_each(|(who, call)| {
				let result = call.dispatch(RawOrigin::Signed(who.clone()).into());
				Self::deposit_event(RawEvent::Dispatched(who, result.is_ok()));
			});

			result.map(|_| ())
		}

		/// Allows block producers to claim a small reward for evicting a contract. If a block producer
		/// fails to do so, a regular users will be allowed to claim the reward.
		///
		/// If contract is not evicted as a result of this call, no actions are taken and
		/// the sender is not eligible for the reward.
		fn claim_surcharge(origin, dest: T::AccountId, aux_sender: Option<T::AccountId>) {
			let origin = origin.into();
			let (signed, rewarded) = match origin {
				Ok(system::RawOrigin::Signed(ref account)) if aux_sender.is_none() => {
					(true, account)
				},
				Ok(system::RawOrigin::None) if aux_sender.is_some() => {
					(false, aux_sender.as_ref().expect("checked above"))
				},
				_ => return Err("Invalid surcharge claim: origin must be signed or \
								inherent and auxiliary sender only provided on inherent")
			};

			// Add some advantage for block producers (who send unsigned extrinsics) by
			// adding a handicap: for signed extrinsics we use a slightly older block number
			// for the eviction check. This can be viewed as if we pushed regular users back in past.
			let handicap = if signed {
				<Module<T>>::signed_claim_handicap()
			} else {
				Zero::zero()
			};

			// If poking the contract has lead to eviction of the contract, give out the rewards.
			if rent::try_evict::<T>(&dest, handicap) == rent::RentOutcome::Evicted {
				T::Currency::deposit_into_existing(rewarded, Self::surcharge_reward())?;
			}
		}

		/// Allows a contract to restore a tombstone by giving its storage.
		///
		/// The contract that wants to restore (i.e. origin of the call, or `msg.sender` in Solidity terms) will compute a
		/// tombstone with its storage and the given code_hash. If the computed tombstone
		/// match the destination one, the destination contract is restored with the rent_allowance` specified,
		/// while the origin sends all its funds to the destination and is removed.
		fn restore_to(
			origin,
			dest: T::AccountId,
			code_hash: CodeHash<T>,
			rent_allowance: BalanceOf<T>,
			delta: Vec<exec::StorageKey>
		) {
			let origin = ensure_signed(origin)?;

			let mut origin_contract = <ContractInfoOf<T>>::get(&origin)
				.and_then(|c| c.get_alive())
				.ok_or("Cannot restore from inexisting or tombstone contract")?;

			let current_block = <system::Module<T>>::block_number();

			if origin_contract.last_write == Some(current_block) {
				return Err("Origin TrieId written in the current block");
			}

			let dest_tombstone = <ContractInfoOf<T>>::get(&dest)
				.and_then(|c| c.get_tombstone())
				.ok_or("Cannot restore to inexisting or alive contract")?;

			let last_write = if !delta.is_empty() {
				Some(current_block)
			} else {
				origin_contract.last_write
			};

			let key_values_taken = delta.iter()
				.filter_map(|key| {
					child::get_raw(&origin_contract.trie_id, &blake2_256(key)).map(|value| {
						child::kill(&origin_contract.trie_id, &blake2_256(key));
						(key, value)
					})
				})
				.collect::<Vec<_>>();

			let tombstone = <TombstoneContractInfo<T>>::new(
				// This operation is cheap enough because last_write (delta not included)
				// is not this block as it has been checked earlier.
				&runtime_io::child_storage_root(&origin_contract.trie_id)[..],
				code_hash,
			);

			if tombstone != dest_tombstone {
				for (key, value) in key_values_taken {
					child::put_raw(&origin_contract.trie_id, &blake2_256(key), &value);
				}

				return Err("Tombstones don't match");
			}

			origin_contract.storage_size -= key_values_taken.iter()
				.map(|(_, value)| value.len() as u32)
				.sum::<u32>();

			<ContractInfoOf<T>>::remove(&origin);
			<ContractInfoOf<T>>::insert(&dest, ContractInfo::Alive(RawAliveContractInfo {
				trie_id: origin_contract.trie_id,
				storage_size: origin_contract.storage_size,
				code_hash,
				rent_allowance,
				deduct_block: current_block,
				last_write,
			}));

			let origin_free_balance = T::Currency::free_balance(&origin);
			T::Currency::make_free_balance_be(&origin, <BalanceOf<T>>::zero());
			T::Currency::deposit_creating(&dest, origin_free_balance);
		}

		fn on_finalize() {
			<GasSpent<T>>::kill();
		}
	}
}

decl_event! {
	pub enum Event<T>
	where
		Balance = BalanceOf<T>,
		<T as system::Trait>::AccountId,
		<T as system::Trait>::Hash
	{
		/// Transfer happened `from` to `to` with given `value` as part of a `call` or `create`.
		Transfer(AccountId, AccountId, Balance),

		/// Contract deployed by address at the specified address.
		Instantiated(AccountId, AccountId),

		/// Code with the specified hash has been stored.
		CodeStored(Hash),

		/// Triggered when the current schedule is updated.
		ScheduleUpdated(u32),

		/// A call was dispatched from the given account. The bool signals whether it was
		/// successful execution or not.
		Dispatched(AccountId, bool),

		/// An event from contract of account.
		Contract(AccountId, Vec<u8>),
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Contract {
		/// Number of block delay an extrinsic claim surcharge has.
		///
		/// When claim surchage is called by an extrinsic the rent is checked
		/// for current_block - delay
		SignedClaimHandicap get(signed_claim_handicap) config(): T::BlockNumber;
		/// The minimum amount required to generate a tombstone.
		TombstoneDeposit get(tombstone_deposit) config(): BalanceOf<T>;
		/// Size of a contract at the time of creation. This is a simple way to ensure
		/// that empty contracts eventually gets deleted.
		StorageSizeOffset get(storage_size_offset) config(): u32;
		/// Price of a byte of storage per one block interval. Should be greater than 0.
		RentByteFee get(rent_byte_price) config(): BalanceOf<T>;
		/// The amount of funds a contract should deposit in order to offset
		/// the cost of one byte.
		///
		/// Let's suppose the deposit is 1,000 BU (balance units)/byte and the rent is 1 BU/byte/day,
		/// then a contract with 1,000,000 BU that uses 1,000 bytes of storage would pay no rent.
		/// But if the balance reduced to 500,000 BU and the storage stayed the same at 1,000,
		/// then it would pay 500 BU/day.
		RentDepositOffset get(rent_deposit_offset) config(): BalanceOf<T>;
		/// Reward that is received by the party whose touch has led
		/// to removal of a contract.
		SurchargeReward get(surcharge_reward) config(): BalanceOf<T>;
		/// The fee required to make a transfer.
		TransferFee get(transfer_fee) config(): BalanceOf<T>;
		/// The fee required to create an account.
		CreationFee get(creation_fee) config(): BalanceOf<T>;
		/// The fee to be paid for making a transaction; the base.
		TransactionBaseFee get(transaction_base_fee) config(): BalanceOf<T>;
		/// The fee to be paid for making a transaction; the per-byte portion.
		TransactionByteFee get(transaction_byte_fee) config(): BalanceOf<T>;
		/// The fee required to create a contract instance.
		ContractFee get(contract_fee) config(): BalanceOf<T> = 21.into();
		/// The base fee charged for calling into a contract.
		CallBaseFee get(call_base_fee) config(): T::Gas = 135.into();
		/// The base fee charged for creating a contract.
		CreateBaseFee get(create_base_fee) config(): T::Gas = 175.into();
		/// The price of one unit of gas.
		GasPrice get(gas_price) config(): BalanceOf<T> = 1.into();
		/// The maximum nesting level of a call/create stack.
		MaxDepth get(max_depth) config(): u32 = 100;
		/// The maximum amount of gas that could be expended per block.
		BlockGasLimit get(block_gas_limit) config(): T::Gas = 10_000_000.into();
		/// Gas spent so far in this block.
		GasSpent get(gas_spent): T::Gas;
		/// Current cost schedule for contracts.
		CurrentSchedule get(current_schedule) config(): Schedule<T::Gas> = Schedule::default();
		/// A mapping from an original code hash to the original code, untouched by instrumentation.
		pub PristineCode: map CodeHash<T> => Option<Vec<u8>>;
		/// A mapping between an original code hash and instrumented wasm code, ready for execution.
		pub CodeStorage: map CodeHash<T> => Option<wasm::PrefabWasmModule>;
		/// The subtrie counter.
		pub AccountCounter: u64 = 0;
		/// The code associated with a given account.
		pub ContractInfoOf: map T::AccountId => Option<ContractInfo<T>>;
	}
}

impl<T: Trait> OnFreeBalanceZero<T::AccountId> for Module<T> {
	fn on_free_balance_zero(who: &T::AccountId) {
		if let Some(ContractInfo::Alive(info)) = <ContractInfoOf<T>>::get(who) {
			child::kill_storage(&info.trie_id);
		}
		<ContractInfoOf<T>>::remove(who);
	}
}

/// In-memory cache of configuration values.
///
/// We assume that these values can't be changed in the
/// course of transaction execution.
pub struct Config<T: Trait> {
	pub schedule: Schedule<T::Gas>,
	pub existential_deposit: BalanceOf<T>,
	pub max_depth: u32,
	pub contract_account_instantiate_fee: BalanceOf<T>,
	pub account_create_fee: BalanceOf<T>,
	pub transfer_fee: BalanceOf<T>,
	pub call_base_fee: T::Gas,
	pub instantiate_base_fee: T::Gas,
}

impl<T: Trait> Config<T> {
	fn preload() -> Config<T> {
		Config {
			schedule: <Module<T>>::current_schedule(),
			existential_deposit: T::Currency::minimum_balance(),
			max_depth: <Module<T>>::max_depth(),
			contract_account_instantiate_fee: <Module<T>>::contract_fee(),
			account_create_fee: <Module<T>>::creation_fee(),
			transfer_fee: <Module<T>>::transfer_fee(),
			call_base_fee: <Module<T>>::call_base_fee(),
			instantiate_base_fee: <Module<T>>::create_base_fee(),
		}
	}
}

/// Definition of the cost schedule and other parameterizations for wasm vm.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Clone, Encode, Decode, PartialEq, Eq)]
pub struct Schedule<Gas> {
	/// Version of the schedule.
	pub version: u32,

	/// Cost of putting a byte of code into storage.
	pub put_code_per_byte_cost: Gas,

	/// Gas cost of a growing memory by single page.
	pub grow_mem_cost: Gas,

	/// Gas cost of a regular operation.
	pub regular_op_cost: Gas,

	/// Gas cost per one byte returned.
	pub return_data_per_byte_cost: Gas,

	/// Gas cost to deposit an event; the per-byte portion.
	pub event_data_per_byte_cost: Gas,

	/// Gas cost to deposit an event; the cost per topic.
	pub event_per_topic_cost: Gas,

	/// Gas cost to deposit an event; the base.
	pub event_base_cost: Gas,

	/// Gas cost per one byte read from the sandbox memory.
	pub sandbox_data_read_cost: Gas,

	/// Gas cost per one byte written to the sandbox memory.
	pub sandbox_data_write_cost: Gas,

	/// The maximum number of topics supported by an event.
	pub max_event_topics: u32,

	/// Maximum allowed stack height.
	///
	/// See https://wiki.parity.io/WebAssembly-StackHeight to find out
	/// how the stack frame cost is calculated.
	pub max_stack_height: u32,

	/// Maximum number of memory pages allowed for a contract.
	pub max_memory_pages: u32,

	/// Whether the `ext_println` function is allowed to be used contracts.
	/// MUST only be enabled for `dev` chains, NOT for production chains
	pub enable_println: bool,

	/// The maximum length of a subject used for PRNG generation.
	pub max_subject_len: u32,
}

impl<Gas: From<u32>> Default for Schedule<Gas> {
	fn default() -> Schedule<Gas> {
		Schedule {
			version: 0,
			put_code_per_byte_cost: 1.into(),
			grow_mem_cost: 1.into(),
			regular_op_cost: 1.into(),
			return_data_per_byte_cost: 1.into(),
			event_data_per_byte_cost: 1.into(),
			event_per_topic_cost: 1.into(),
			event_base_cost: 1.into(),
			sandbox_data_read_cost: 1.into(),
			sandbox_data_write_cost: 1.into(),
			max_event_topics: 4,
			max_stack_height: 64 * 1024,
			max_memory_pages: 16,
			enable_println: false,
			max_subject_len: 32,
		}
	}
}
