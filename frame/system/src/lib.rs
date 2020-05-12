// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # System Module
//!
//! The System module provides low-level access to core types and cross-cutting utilities.
//! It acts as the base layer for other pallets to interact with the Substrate framework components.
//!
//! - [`system::Trait`](./trait.Trait.html)
//!
//! ## Overview
//!
//! The System module defines the core data types used in a Substrate runtime.
//! It also provides several utility functions (see [`Module`](./struct.Module.html)) for other FRAME pallets.
//!
//! In addition, it manages the storage items for extrinsics data, indexes, event records, and digest items,
//! among other things that support the execution of the current block.
//!
//! It also handles low-level tasks like depositing logs, basic set up and take down of
//! temporary storage entries, and access to previous block hashes.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! The System module does not implement any dispatchable functions.
//!
//! ### Public Functions
//!
//! See the [`Module`](./struct.Module.html) struct for details of publicly available functions.
//!
//! ### Signed Extensions
//!
//! The System module defines the following extensions:
//!
//!   - [`CheckWeight`]: Checks the weight and length of the block and ensure that it does not
//!     exceed the limits.
//!   - [`CheckNonce`]: Checks the nonce of the transaction. Contains a single payload of type
//!     `T::Index`.
//!   - [`CheckEra`]: Checks the era of the transaction. Contains a single payload of type `Era`.
//!   - [`CheckGenesis`]: Checks the provided genesis hash of the transaction. Must be a part of the
//!     signed payload of the transaction.
//!   - [`CheckVersion`]: Checks that the runtime version is the same as the one encoded in the
//!     transaction.
//!
//! Lookup the runtime aggregator file (e.g. `node/runtime`) to see the full list of signed
//! extensions included in a chain.
//!
//! ## Usage
//!
//! ### Prerequisites
//!
//! Import the System module and derive your module's configuration trait from the system trait.
//!
//! ### Example - Get extrinsic count and parent hash for the current block
//!
//! ```
//! use frame_support::{decl_module, dispatch};
//! use frame_system::{self as system, ensure_signed};
//!
//! pub trait Trait: system::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		#[weight = 0]
//! 		pub fn system_module_example(origin) -> dispatch::DispatchResult {
//! 			let _sender = ensure_signed(origin)?;
//! 			let _extrinsic_count = <system::Module<T>>::extrinsic_count();
//! 			let _parent_hash = <system::Module<T>>::parent_hash();
//! 			Ok(())
//! 		}
//! 	}
//! }
//! # fn main() { }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::Serialize;
use sp_std::prelude::*;
#[cfg(any(feature = "std", test))]
use sp_std::map;
use sp_std::convert::Infallible;
use sp_std::marker::PhantomData;
use sp_std::fmt::Debug;
use sp_version::RuntimeVersion;
use sp_runtime::{
	RuntimeDebug, Perbill, DispatchOutcome, DispatchError, DispatchResult,
	generic::{self, Era},
	transaction_validity::{
		ValidTransaction, TransactionPriority, TransactionLongevity, TransactionValidityError,
		InvalidTransaction, TransactionValidity,
	},
	traits::{
		self, CheckEqual, AtLeast32Bit, Zero, SignedExtension, Lookup, LookupError,
		SimpleBitOps, Hash, Member, MaybeDisplay, BadOrigin, SaturatedConversion,
		MaybeSerialize, MaybeSerializeDeserialize, MaybeMallocSizeOf, StaticLookup, One, Bounded,
		Dispatchable, DispatchInfoOf, PostDispatchInfoOf,
	},
};

use sp_core::{ChangesTrieConfiguration, storage::well_known_keys};
use frame_support::{
	decl_module, decl_event, decl_storage, decl_error, Parameter, ensure, debug,
	storage,
	traits::{
		Contains, Get, ModuleToIndex, OnNewAccount, OnKilledAccount, IsDeadAccount, Happened,
		StoredMap, EnsureOrigin,
	},
	weights::{
		Weight, RuntimeDbWeight, DispatchInfo, PostDispatchInfo, DispatchClass,
		FunctionOf, Pays,
	}
};
use codec::{Encode, Decode, FullCodec, EncodeLike};

#[cfg(any(feature = "std", test))]
use sp_io::TestExternalities;

pub mod offchain;

/// Compute the trie root of a list of extrinsics.
pub fn extrinsics_root<H: Hash, E: codec::Encode>(extrinsics: &[E]) -> H::Output {
	extrinsics_data_root::<H>(extrinsics.iter().map(codec::Encode::encode).collect())
}

/// Compute the trie root of a list of extrinsics.
pub fn extrinsics_data_root<H: Hash>(xts: Vec<Vec<u8>>) -> H::Output {
	H::ordered_trie_root(xts)
}

pub trait Trait: 'static + Eq + Clone {
	/// The aggregated `Origin` type used by dispatchable calls.
	type Origin:
		Into<Result<RawOrigin<Self::AccountId>, Self::Origin>>
		+ From<RawOrigin<Self::AccountId>>
		+ Clone;

	/// The aggregated `Call` type.
	type Call: Dispatchable + Debug;

	/// Account index (aka nonce) type. This stores the number of previous transactions associated
	/// with a sender account.
	type Index:
		Parameter + Member + MaybeSerialize + Debug + Default + MaybeDisplay + AtLeast32Bit
		+ Copy;

	/// The block number type used by the runtime.
	type BlockNumber:
		Parameter + Member + MaybeSerializeDeserialize + Debug + MaybeDisplay + AtLeast32Bit
		+ Default + Bounded + Copy + sp_std::hash::Hash + sp_std::str::FromStr + MaybeMallocSizeOf;

	/// The output of the `Hashing` function.
	type Hash:
		Parameter + Member + MaybeSerializeDeserialize + Debug + MaybeDisplay + SimpleBitOps + Ord
		+ Default + Copy + CheckEqual + sp_std::hash::Hash + AsRef<[u8]> + AsMut<[u8]> + MaybeMallocSizeOf;

	/// The hashing system (algorithm) being used in the runtime (e.g. Blake2).
	type Hashing: Hash<Output = Self::Hash>;

	/// The user account identifier type for the runtime.
	type AccountId: Parameter + Member + MaybeSerializeDeserialize + Debug + MaybeDisplay + Ord
		+ Default;

	/// Converting trait to take a source type and convert to `AccountId`.
	///
	/// Used to define the type and conversion mechanism for referencing accounts in transactions.
	/// It's perfectly reasonable for this to be an identity conversion (with the source type being
	/// `AccountId`), but other modules (e.g. Indices module) may provide more functional/efficient
	/// alternatives.
	type Lookup: StaticLookup<Target = Self::AccountId>;

	/// The block header.
	type Header: Parameter + traits::Header<
		Number = Self::BlockNumber,
		Hash = Self::Hash,
	>;

	/// The aggregated event type of the runtime.
	type Event: Parameter + Member + From<Event<Self>> + Debug;

	/// Maximum number of block number to block hash mappings to keep (oldest pruned first).
	type BlockHashCount: Get<Self::BlockNumber>;

	/// The maximum weight of a block.
	type MaximumBlockWeight: Get<Weight>;

	/// The weight of runtime database operations the runtime can invoke.
	type DbWeight: Get<RuntimeDbWeight>;

	/// The base weight of executing a block, independent of the transactions in the block.
	type BlockExecutionWeight: Get<Weight>;

	/// The base weight of an Extrinsic in the block, independent of the of extrinsic being executed.
	type ExtrinsicBaseWeight: Get<Weight>;

	/// The maximum length of a block (in bytes).
	type MaximumBlockLength: Get<u32>;

	/// The portion of the block that is available to normal transaction. The rest can only be used
	/// by operational transactions. This can be applied to any resource limit managed by the system
	/// module, including weight and length.
	type AvailableBlockRatio: Get<Perbill>;

	/// Get the chain's current version.
	type Version: Get<RuntimeVersion>;

	/// Convert a module to its index in the runtime.
	///
	/// Expects the `ModuleToIndex` type that is being generated by `construct_runtime!` in the
	/// runtime. For tests it is okay to use `()` as type (returns `0` for each input).
	type ModuleToIndex: ModuleToIndex;

	/// Data to be associated with an account (other than nonce/transaction counter, which this
	/// module does regardless).
	type AccountData: Member + FullCodec + Clone + Default;

	/// Handler for when a new account has just been created.
	type OnNewAccount: OnNewAccount<Self::AccountId>;

	/// A function that is invoked when an account has been determined to be dead.
	///
	/// All resources should be cleaned up associated with the given account.
	type OnKilledAccount: OnKilledAccount<Self::AccountId>;
}

pub type DigestOf<T> = generic::Digest<<T as Trait>::Hash>;
pub type DigestItemOf<T> = generic::DigestItem<<T as Trait>::Hash>;

pub type Key = Vec<u8>;
pub type KeyValue = (Vec<u8>, Vec<u8>);

/// A phase of a block's execution.
#[derive(Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, PartialEq, Eq, Clone))]
pub enum Phase {
	/// Applying an extrinsic.
	ApplyExtrinsic(u32),
	/// Finalizing the block.
	Finalization,
	/// Initializing the block.
	Initialization,
}

impl Default for Phase {
	fn default() -> Self {
		Self::Initialization
	}
}

/// Record of an event happening.
#[derive(Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, PartialEq, Eq, Clone))]
pub struct EventRecord<E: Parameter + Member, T> {
	/// The phase of the block it happened in.
	pub phase: Phase,
	/// The event itself.
	pub event: E,
	/// The list of the topics this event has.
	pub topics: Vec<T>,
}

/// Origin for the System module.
#[derive(PartialEq, Eq, Clone, RuntimeDebug)]
pub enum RawOrigin<AccountId> {
	/// The system itself ordained this dispatch to happen: this is the highest privilege level.
	Root,
	/// It is signed by some public key and we provide the `AccountId`.
	Signed(AccountId),
	/// It is signed by nobody, can be either:
	/// * included and agreed upon by the validators anyway,
	/// * or unsigned transaction validated by a module.
	None,
}

impl<AccountId> From<Option<AccountId>> for RawOrigin<AccountId> {
	fn from(s: Option<AccountId>) -> RawOrigin<AccountId> {
		match s {
			Some(who) => RawOrigin::Signed(who),
			None => RawOrigin::None,
		}
	}
}

/// Exposed trait-generic origin type.
pub type Origin<T> = RawOrigin<<T as Trait>::AccountId>;

// Create a Hash with 69 for each byte,
// only used to build genesis config.
#[cfg(feature = "std")]
fn hash69<T: AsMut<[u8]> + Default>() -> T {
	let mut h = T::default();
	h.as_mut().iter_mut().for_each(|byte| *byte = 69);
	h
}

/// This type alias represents an index of an event.
///
/// We use `u32` here because this index is used as index for `Events<T>`
/// which can't contain more than `u32::max_value()` items.
type EventIndex = u32;

/// Type used to encode the number of references an account has.
pub type RefCount = u8;

/// Information of an account.
#[derive(Clone, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode)]
pub struct AccountInfo<Index, AccountData> {
	/// The number of transactions this account has sent.
	pub nonce: Index,
	/// The number of other modules that currently depend on this account's existence. The account
	/// cannot be reaped until this is zero.
	pub refcount: RefCount,
	/// The additional data that belongs to this account. Used to store the balance(s) in a lot of
	/// chains.
	pub data: AccountData,
}

/// Stores the `spec_version` and `spec_name` of when the last runtime upgrade
/// happened.
#[derive(sp_runtime::RuntimeDebug, Encode, Decode)]
#[cfg_attr(feature = "std", derive(PartialEq))]
pub struct LastRuntimeUpgradeInfo {
	pub spec_version: codec::Compact<u32>,
	pub spec_name: sp_runtime::RuntimeString,
}

impl LastRuntimeUpgradeInfo {
	/// Returns if the runtime was upgraded in comparison of `self` and `current`.
	///
	/// Checks if either the `spec_version` increased or the `spec_name` changed.
	pub fn was_upgraded(&self, current: &sp_version::RuntimeVersion) -> bool {
		current.spec_version > self.spec_version.0 || current.spec_name != self.spec_name
	}
}

impl From<sp_version::RuntimeVersion> for LastRuntimeUpgradeInfo {
	fn from(version: sp_version::RuntimeVersion) -> Self {
		Self {
			spec_version: version.spec_version.into(),
			spec_name: version.spec_name,
		}
	}
}

/// An object to track the currently used extrinsic weight in a block.
#[derive(Clone, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode)]
pub struct ExtrinsicsWeight {
	normal: Weight,
	operational: Weight,
}

impl ExtrinsicsWeight {
	/// Returns the total weight consumed by all extrinsics in the block.
	pub fn total(&self) -> Weight {
		self.normal.saturating_add(self.operational)
	}

	/// Add some weight of a specific dispatch class, saturating at the numeric bounds of `Weight`.
	pub fn add(&mut self, weight: Weight, class: DispatchClass) {
		let value = self.get_mut(class);
		*value = value.saturating_add(weight);
	}

	/// Try to add some weight of a specific dispatch class, returning Err(()) if overflow would occur.
	pub fn checked_add(&mut self, weight: Weight, class: DispatchClass) -> Result<(), ()> {
		let value = self.get_mut(class);
		*value = value.checked_add(weight).ok_or(())?;
		Ok(())
	}

	/// Subtract some weight of a specific dispatch class, saturating at the numeric bounds of `Weight`.
	pub fn sub(&mut self, weight: Weight, class: DispatchClass) {
		let value = self.get_mut(class);
		*value = value.saturating_sub(weight);
	}

	/// Get the current weight of a specific dispatch class.
	pub fn get(&self, class: DispatchClass) -> Weight {
		match class {
			DispatchClass::Operational => self.operational,
			DispatchClass::Normal | DispatchClass::Mandatory => self.normal,
		}
	}

	/// Get a mutable reference to the current weight of a specific dispatch class.
	fn get_mut(&mut self, class: DispatchClass) -> &mut Weight {
		match class {
			DispatchClass::Operational => &mut self.operational,
			DispatchClass::Normal | DispatchClass::Mandatory => &mut self.normal,
		}
	}

	/// Set the weight of a specific dispatch class.
	pub fn put(&mut self, new: Weight, class: DispatchClass) {
		*self.get_mut(class) = new;
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as System {
		/// The full account information for a particular account ID.
		pub Account get(fn account):
			map hasher(blake2_128_concat) T::AccountId => AccountInfo<T::Index, T::AccountData>;

		/// Total extrinsics count for the current block.
		ExtrinsicCount: Option<u32>;

		/// Total weight for all extrinsics for the current block.
		AllExtrinsicsWeight: ExtrinsicsWeight;

		/// Total length (in bytes) for all extrinsics put together, for the current block.
		AllExtrinsicsLen: Option<u32>;

		/// Map of block numbers to block hashes.
		pub BlockHash get(fn block_hash) build(|_| vec![(T::BlockNumber::zero(), hash69())]):
			map hasher(twox_64_concat) T::BlockNumber => T::Hash;

		/// Extrinsics data for the current block (maps an extrinsic's index to its data).
		ExtrinsicData get(fn extrinsic_data): map hasher(twox_64_concat) u32 => Vec<u8>;

		/// The current block number being processed. Set by `execute_block`.
		Number get(fn block_number): T::BlockNumber;

		/// Hash of the previous block.
		ParentHash get(fn parent_hash) build(|_| hash69()): T::Hash;

		/// Extrinsics root of the current block, also part of the block header.
		ExtrinsicsRoot get(fn extrinsics_root): T::Hash;

		/// Digest of the current block, also part of the block header.
		Digest get(fn digest): DigestOf<T>;

		/// Events deposited for the current block.
		Events get(fn events): Vec<EventRecord<T::Event, T::Hash>>;

		/// The number of events in the `Events<T>` list.
		EventCount get(fn event_count): EventIndex;

		// TODO: https://github.com/paritytech/substrate/issues/2553
		// Possibly, we can improve it by using something like:
		// `Option<(BlockNumber, Vec<EventIndex>)>`, however in this case we won't be able to use
		// `EventTopics::append`.

		/// Mapping between a topic (represented by T::Hash) and a vector of indexes
		/// of events in the `<Events<T>>` list.
		///
		/// All topic vectors have deterministic storage locations depending on the topic. This
		/// allows light-clients to leverage the changes trie storage tracking mechanism and
		/// in case of changes fetch the list of events of interest.
		///
		/// The value has the type `(T::BlockNumber, EventIndex)` because if we used only just
		/// the `EventIndex` then in case if the topic has the same contents on the next block
		/// no notification will be triggered thus the event might be lost.
		EventTopics get(fn event_topics): map hasher(blake2_128_concat) T::Hash => Vec<(T::BlockNumber, EventIndex)>;

		/// Stores the `spec_version` and `spec_name` of when the last runtime upgrade happened.
		pub LastRuntimeUpgrade build(|_| Some(LastRuntimeUpgradeInfo::from(T::Version::get()))): Option<LastRuntimeUpgradeInfo>;

		/// The execution phase of the block.
		ExecutionPhase: Option<Phase>;
	}
	add_extra_genesis {
		config(changes_trie_config): Option<ChangesTrieConfiguration>;
		#[serde(with = "sp_core::bytes")]
		config(code): Vec<u8>;

		build(|config: &GenesisConfig| {
			use codec::Encode;

			sp_io::storage::set(well_known_keys::CODE, &config.code);
			sp_io::storage::set(well_known_keys::EXTRINSIC_INDEX, &0u32.encode());

			if let Some(ref changes_trie_config) = config.changes_trie_config {
				sp_io::storage::set(
					well_known_keys::CHANGES_TRIE_CONFIG,
					&changes_trie_config.encode(),
				);
			}
		});
	}
}

decl_event!(
	/// Event for the System module.
	pub enum Event<T> where AccountId = <T as Trait>::AccountId {
		/// An extrinsic completed successfully.
		ExtrinsicSuccess(DispatchInfo),
		/// An extrinsic failed.
		ExtrinsicFailed(DispatchError, DispatchInfo),
		/// `:code` was updated.
		CodeUpdated,
		/// A new account was created.
		NewAccount(AccountId),
		/// An account was reaped.
		KilledAccount(AccountId),
	}
);

decl_error! {
	/// Error for the System module
	pub enum Error for Module<T: Trait> {
		/// The name of specification does not match between the current runtime
		/// and the new runtime.
		InvalidSpecName,
		/// The specification version is not allowed to decrease between the current runtime
		/// and the new runtime.
		SpecVersionNeedsToIncrease,
		/// Failed to extract the runtime version from the new runtime.
		///
		/// Either calling `Core_version` or decoding `RuntimeVersion` failed.
		FailedToExtractRuntimeVersion,
		/// Suicide called when the account has non-default composite data.
		NonDefaultComposite,
		/// There is a non-zero reference count preventing the account from being purged.
		NonZeroRefCount,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		/// The maximum number of blocks to allow in mortal eras.
		const BlockHashCount: T::BlockNumber = T::BlockHashCount::get();

		/// The maximum weight of a block.
		const MaximumBlockWeight: Weight = T::MaximumBlockWeight::get();

		/// The weight of runtime database operations the runtime can invoke.
		const DbWeight: RuntimeDbWeight = T::DbWeight::get();

		/// The base weight of executing a block, independent of the transactions in the block.
		const BlockExecutionWeight: Weight = T::BlockExecutionWeight::get();

		/// The base weight of an Extrinsic in the block, independent of the of extrinsic being executed.
		const ExtrinsicBaseWeight: Weight = T::ExtrinsicBaseWeight::get();

		/// The maximum length of a block (in bytes).
		const MaximumBlockLength: u32 = T::MaximumBlockLength::get();

		/// A dispatch that will fill the block weight up to the given ratio.
		// TODO: This should only be available for testing, rather than in general usage, but
		// that's not possible at present (since it's within the decl_module macro).
		#[weight = FunctionOf(
			|(ratio,): (&Perbill,)| *ratio * T::MaximumBlockWeight::get(),
			DispatchClass::Operational,
			Pays::Yes,
		)]
		fn fill_block(origin, _ratio: Perbill) {
			ensure_root(origin)?;
		}

		/// Make some on-chain remark.
		///
		/// # <weight>
		/// - `O(1)`
		/// - Base Weight: 0.665 µs, independent of remark length.
		/// - No DB operations.
		/// # </weight>
		#[weight = 700_000]
		fn remark(origin, _remark: Vec<u8>) {
			ensure_signed(origin)?;
		}

		/// Set the number of pages in the WebAssembly environment's heap.
		///
		/// # <weight>
		/// - `O(1)`
		/// - 1 storage write.
		/// - Base Weight: 1.405 µs
		/// - 1 write to HEAP_PAGES
		/// # </weight>
		#[weight = (T::DbWeight::get().writes(1) + 1_500_000, DispatchClass::Operational)]
		fn set_heap_pages(origin, pages: u64) {
			ensure_root(origin)?;
			storage::unhashed::put_raw(well_known_keys::HEAP_PAGES, &pages.encode());
		}

		/// Set the new runtime code.
		///
		/// # <weight>
		/// - `O(C + S)` where `C` length of `code` and `S` complexity of `can_set_code`
		/// - 1 storage write (codec `O(C)`).
		/// - 1 call to `can_set_code`: `O(S)` (calls `sp_io::misc::runtime_version` which is expensive).
		/// - 1 event.
		/// The weight of this function is dependent on the runtime, but generally this is very expensive.
		/// We will treat this as a full block.
		/// # </weight>
		#[weight = (T::MaximumBlockWeight::get(), DispatchClass::Operational)]
		pub fn set_code(origin, code: Vec<u8>) {
			Self::can_set_code(origin, &code)?;

			storage::unhashed::put_raw(well_known_keys::CODE, &code);
			Self::deposit_event(RawEvent::CodeUpdated);
		}

		/// Set the new runtime code without doing any checks of the given `code`.
		///
		/// # <weight>
		/// - `O(C)` where `C` length of `code`
		/// - 1 storage write (codec `O(C)`).
		/// - 1 event.
		/// The weight of this function is dependent on the runtime. We will treat this as a full block.
		/// # </weight>
		#[weight = (T::MaximumBlockWeight::get(), DispatchClass::Operational)]
		pub fn set_code_without_checks(origin, code: Vec<u8>) {
			ensure_root(origin)?;
			storage::unhashed::put_raw(well_known_keys::CODE, &code);
			Self::deposit_event(RawEvent::CodeUpdated);
		}

		/// Set the new changes trie configuration.
		///
		/// # <weight>
		/// - `O(1)`
		/// - 1 storage write or delete (codec `O(1)`).
		/// - 1 call to `deposit_log`: Uses `append` API, so O(1)
		/// - Base Weight: 7.218 µs
		/// - DB Weight:
		///     - Writes: Changes Trie, System Digest
		/// # </weight>
		#[weight = (T::DbWeight::get().writes(2) + 10_000_000, DispatchClass::Operational)]
		pub fn set_changes_trie_config(origin, changes_trie_config: Option<ChangesTrieConfiguration>) {
			ensure_root(origin)?;
			match changes_trie_config.clone() {
				Some(changes_trie_config) => storage::unhashed::put_raw(
					well_known_keys::CHANGES_TRIE_CONFIG,
					&changes_trie_config.encode(),
				),
				None => storage::unhashed::kill(well_known_keys::CHANGES_TRIE_CONFIG),
			}

			let log = generic::DigestItem::ChangesTrieSignal(
				generic::ChangesTrieSignal::NewConfiguration(changes_trie_config),
			);
			Self::deposit_log(log.into());
		}

		/// Set some items of storage.
		///
		/// # <weight>
		/// - `O(I)` where `I` length of `items`
		/// - `I` storage writes (`O(1)`).
		/// - Base Weight: 0.568 * i µs
		/// - Writes: Number of items
		/// # </weight>
		#[weight = FunctionOf(
			|(items,): (&Vec<KeyValue>,)| {
				T::DbWeight::get().writes(items.len() as Weight)
					.saturating_add((items.len() as Weight).saturating_mul(600_000))
			},
			DispatchClass::Operational,
			Pays::Yes,
		)]
		fn set_storage(origin, items: Vec<KeyValue>) {
			ensure_root(origin)?;
			for i in &items {
				storage::unhashed::put_raw(&i.0, &i.1);
			}
		}

		/// Kill some items from storage.
		///
		/// # <weight>
		/// - `O(IK)` where `I` length of `keys` and `K` length of one key
		/// - `I` storage deletions.
		/// - Base Weight: .378 * i µs
		/// - Writes: Number of items
		/// # </weight>
		#[weight = FunctionOf(
			|(keys,): (&Vec<Key>,)| {
				T::DbWeight::get().writes(keys.len() as Weight)
					.saturating_add((keys.len() as Weight).saturating_mul(400_000))
			},
			DispatchClass::Operational,
			Pays::Yes,
		)]
		fn kill_storage(origin, keys: Vec<Key>) {
			ensure_root(origin)?;
			for key in &keys {
				storage::unhashed::kill(&key);
			}
		}

		/// Kill all storage items with a key that starts with the given prefix.
		///
		/// **NOTE:** We rely on the Root origin to provide us the number of subkeys under
		/// the prefix we are removing to accurately calculate the weight of this function.
		///
		/// # <weight>
		/// - `O(P)` where `P` amount of keys with prefix `prefix`
		/// - `P` storage deletions.
		/// - Base Weight: 0.834 * P µs
		/// - Writes: Number of subkeys + 1
		/// # </weight>
		#[weight = FunctionOf(
			|(_, &subkeys): (&Key, &u32)| {
				T::DbWeight::get().writes(Weight::from(subkeys) + 1)
					.saturating_add((Weight::from(subkeys) + 1).saturating_mul(850_000))
			},
			DispatchClass::Operational,
			Pays::Yes,
		)]
		fn kill_prefix(origin, prefix: Key, _subkeys: u32) {
			ensure_root(origin)?;
			storage::unhashed::kill_prefix(&prefix);
		}

		/// Kill the sending account, assuming there are no references outstanding and the composite
		/// data is equal to its default value.
		///
		/// # <weight>
		/// - `O(1)`
		/// - 1 storage read and deletion.
		/// --------------------
		/// Base Weight: 8.626 µs
		/// No DB Read or Write operations because caller is already in overlay
		/// # </weight>
		#[weight = (10_000_000, DispatchClass::Operational)]
		fn suicide(origin) {
			let who = ensure_signed(origin)?;
			let account = Account::<T>::get(&who);
			ensure!(account.refcount == 0, Error::<T>::NonZeroRefCount);
			ensure!(account.data == T::AccountData::default(), Error::<T>::NonDefaultComposite);
			Account::<T>::remove(who);
		}
	}
}

pub struct EnsureRoot<AccountId>(sp_std::marker::PhantomData<AccountId>);
impl<
	O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
	AccountId,
> EnsureOrigin<O> for EnsureRoot<AccountId> {
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Root => Ok(()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		O::from(RawOrigin::Root)
	}
}

pub struct EnsureSigned<AccountId>(sp_std::marker::PhantomData<AccountId>);
impl<
	O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
	AccountId: Default,
> EnsureOrigin<O> for EnsureSigned<AccountId> {
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Signed(who) => Ok(who),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		O::from(RawOrigin::Signed(Default::default()))
	}
}

pub struct EnsureSignedBy<Who, AccountId>(sp_std::marker::PhantomData<(Who, AccountId)>);
impl<
	O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
	Who: Contains<AccountId>,
	AccountId: PartialEq + Clone + Ord + Default,
> EnsureOrigin<O> for EnsureSignedBy<Who, AccountId> {
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Signed(ref who) if Who::contains(who) => Ok(who.clone()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		let members = Who::sorted_members();
		let first_member = match members.get(0) {
			Some(account) => account.clone(),
			None => Default::default(),
		};
		O::from(RawOrigin::Signed(first_member.clone()))
	}
}

pub struct EnsureNone<AccountId>(sp_std::marker::PhantomData<AccountId>);
impl<
	O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
	AccountId,
> EnsureOrigin<O> for EnsureNone<AccountId> {
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::None => Ok(()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		O::from(RawOrigin::None)
	}
}

pub struct EnsureNever<T>(sp_std::marker::PhantomData<T>);
impl<O, T> EnsureOrigin<O> for EnsureNever<T> {
	type Success = T;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		Err(o)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		unimplemented!()
	}
}

/// Ensure that the origin `o` represents a signed extrinsic (i.e. transaction).
/// Returns `Ok` with the account that signed the extrinsic or an `Err` otherwise.
pub fn ensure_signed<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<AccountId, BadOrigin>
	where OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>
{
	match o.into() {
		Ok(RawOrigin::Signed(t)) => Ok(t),
		_ => Err(BadOrigin),
	}
}

/// Ensure that the origin `o` represents the root. Returns `Ok` or an `Err` otherwise.
pub fn ensure_root<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), BadOrigin>
	where OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>
{
	match o.into() {
		Ok(RawOrigin::Root) => Ok(()),
		_ => Err(BadOrigin),
	}
}

/// Ensure that the origin `o` represents an unsigned extrinsic. Returns `Ok` or an `Err` otherwise.
pub fn ensure_none<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), BadOrigin>
	where OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>
{
	match o.into() {
		Ok(RawOrigin::None) => Ok(()),
		_ => Err(BadOrigin),
	}
}

/// A type of block initialization to perform.
pub enum InitKind {
	/// Leave inspectable storage entries in state.
	///
	/// i.e. `Events` are not being reset.
	/// Should only be used for off-chain calls,
	/// regular block execution should clear those.
	Inspection,

	/// Reset also inspectable storage entries.
	///
	/// This should be used for regular block execution.
	Full,
}

impl Default for InitKind {
	fn default() -> Self {
		InitKind::Full
	}
}

/// Reference status; can be either referenced or unreferenced.
pub enum RefStatus {
	Referenced,
	Unreferenced,
}

impl<T: Trait> Module<T> {
	/// Deposits an event into this block's event record.
	pub fn deposit_event(event: impl Into<T::Event>) {
		Self::deposit_event_indexed(&[], event.into());
	}

	/// Increment the reference counter on an account.
	pub fn inc_ref(who: &T::AccountId) {
		Account::<T>::mutate(who, |a| a.refcount = a.refcount.saturating_add(1));
	}

	/// Decrement the reference counter on an account. This *MUST* only be done once for every time
	/// you called `inc_ref` on `who`.
	pub fn dec_ref(who: &T::AccountId) {
		Account::<T>::mutate(who, |a| a.refcount = a.refcount.saturating_sub(1));
	}

	/// The number of outstanding references for the account `who`.
	pub fn refs(who: &T::AccountId) -> RefCount {
		Account::<T>::get(who).refcount
	}

	/// True if the account has no outstanding references.
	pub fn allow_death(who: &T::AccountId) -> bool {
		Account::<T>::get(who).refcount == 0
	}

	/// Deposits an event into this block's event record adding this event
	/// to the corresponding topic indexes.
	///
	/// This will update storage entries that correspond to the specified topics.
	/// It is expected that light-clients could subscribe to this topics.
	pub fn deposit_event_indexed(topics: &[T::Hash], event: T::Event) {
		let block_number = Self::block_number();
		// Don't populate events on genesis.
		if block_number.is_zero() { return }

		let phase = ExecutionPhase::get().unwrap_or_default();
		let event = EventRecord {
			phase,
			event,
			topics: topics.iter().cloned().collect::<Vec<_>>(),
		};

		// Index of the to be added event.
		let event_idx = {
			let old_event_count = EventCount::get();
			let new_event_count = match old_event_count.checked_add(1) {
				// We've reached the maximum number of events at this block, just
				// don't do anything and leave the event_count unaltered.
				None => return,
				Some(nc) => nc,
			};
			EventCount::put(new_event_count);
			old_event_count
		};

		Events::<T>::append(&event);

		for topic in topics {
			<EventTopics<T>>::append(topic, &(block_number, event_idx));
		}
	}

	/// Gets the index of extrinsic that is currently executing.
	pub fn extrinsic_index() -> Option<u32> {
		storage::unhashed::get(well_known_keys::EXTRINSIC_INDEX)
	}

	/// Gets extrinsics count.
	pub fn extrinsic_count() -> u32 {
		ExtrinsicCount::get().unwrap_or_default()
	}

	/// Gets the weight of all executed extrinsics.
	pub fn all_extrinsics_weight() -> ExtrinsicsWeight {
		AllExtrinsicsWeight::get()
	}

	pub fn all_extrinsics_len() -> u32 {
		AllExtrinsicsLen::get().unwrap_or_default()
	}

	/// Inform the system module of some additional weight that should be accounted for, in the
	/// current block.
	///
	/// NOTE: use with extra care; this function is made public only be used for certain modules
	/// that need it. A runtime that does not have dynamic calls should never need this and should
	/// stick to static weights. A typical use case for this is inner calls or smart contract calls.
	/// Furthermore, it only makes sense to use this when it is presumably  _cheap_ to provide the
	/// argument `weight`; In other words, if this function is to be used to account for some
	/// unknown, user provided call's weight, it would only make sense to use it if you are sure you
	/// can rapidly compute the weight of the inner call.
	///
	/// Even more dangerous is to note that this function does NOT take any action, if the new sum
	/// of block weight is more than the block weight limit. This is what the _unchecked_.
	///
	/// Another potential use-case could be for the `on_initialize` and `on_finalize` hooks.
	pub fn register_extra_weight_unchecked(weight: Weight, class: DispatchClass) {
		AllExtrinsicsWeight::mutate(|current_weight| {
			current_weight.add(weight, class);
		});
	}

	/// Start the execution of a particular block.
	pub fn initialize(
		number: &T::BlockNumber,
		parent_hash: &T::Hash,
		txs_root: &T::Hash,
		digest: &DigestOf<T>,
		kind: InitKind,
	) {
		// populate environment
		ExecutionPhase::put(Phase::Initialization);
		storage::unhashed::put(well_known_keys::EXTRINSIC_INDEX, &0u32);
		<Number<T>>::put(number);
		<Digest<T>>::put(digest);
		<ParentHash<T>>::put(parent_hash);
		<BlockHash<T>>::insert(*number - One::one(), parent_hash);
		<ExtrinsicsRoot<T>>::put(txs_root);

		if let InitKind::Full = kind {
			<Events<T>>::kill();
			EventCount::kill();
			<EventTopics<T>>::remove_all();
		}
	}

	/// Remove temporary "environment" entries in storage.
	pub fn finalize() -> T::Header {
		ExecutionPhase::kill();
		ExtrinsicCount::kill();
		AllExtrinsicsWeight::kill();
		AllExtrinsicsLen::kill();

		let number = <Number<T>>::take();
		let parent_hash = <ParentHash<T>>::take();
		let mut digest = <Digest<T>>::take();
		let extrinsics_root = <ExtrinsicsRoot<T>>::take();

		// move block hash pruning window by one block
		let block_hash_count = <T::BlockHashCount>::get();
		if number > block_hash_count {
			let to_remove = number - block_hash_count - One::one();

			// keep genesis hash
			if to_remove != Zero::zero() {
				<BlockHash<T>>::remove(to_remove);
			}
		}

		let storage_root = T::Hash::decode(&mut &sp_io::storage::root()[..])
			.expect("Node is configured to use the same hash; qed");
		let storage_changes_root = sp_io::storage::changes_root(&parent_hash.encode());

		// we can't compute changes trie root earlier && put it to the Digest
		// because it will include all currently existing temporaries.
		if let Some(storage_changes_root) = storage_changes_root {
			let item = generic::DigestItem::ChangesTrieRoot(
				T::Hash::decode(&mut &storage_changes_root[..])
					.expect("Node is configured to use the same hash; qed")
			);
			digest.push(item);
		}

		// The following fields
		//
		// - <Events<T>>
		// - <EventCount<T>>
		// - <EventTopics<T>>
		//
		// stay to be inspected by the client and will be cleared by `Self::initialize`.

		<T::Header as traits::Header>::new(number, extrinsics_root, storage_root, parent_hash, digest)
	}

	/// Deposits a log and ensures it matches the block's log data.
	///
	/// # <weight>
	/// - `O(1)`
	/// - 1 storage write (codec `O(1)`)
	/// # </weight>
	pub fn deposit_log(item: DigestItemOf<T>) {
		<Digest<T>>::append(item);
	}

	/// Get the basic externalities for this module, useful for tests.
	#[cfg(any(feature = "std", test))]
	pub fn externalities() -> TestExternalities {
		TestExternalities::new(sp_core::storage::Storage {
			top: map![
				<BlockHash<T>>::hashed_key_for(T::BlockNumber::zero()) => [69u8; 32].encode(),
				<Number<T>>::hashed_key().to_vec() => T::BlockNumber::one().encode(),
				<ParentHash<T>>::hashed_key().to_vec() => [69u8; 32].encode()
			],
			children_default: map![],
		})
	}

	/// Set the block number to something in particular. Can be used as an alternative to
	/// `initialize` for tests that don't need to bother with the other environment entries.
	#[cfg(any(feature = "std", feature = "runtime-benchmarks", test))]
	pub fn set_block_number(n: T::BlockNumber) {
		<Number<T>>::put(n);
	}

	/// Sets the index of extrinsic that is currently executing.
	#[cfg(any(feature = "std", test))]
	pub fn set_extrinsic_index(extrinsic_index: u32) {
		storage::unhashed::put(well_known_keys::EXTRINSIC_INDEX, &extrinsic_index)
	}

	/// Set the parent hash number to something in particular. Can be used as an alternative to
	/// `initialize` for tests that don't need to bother with the other environment entries.
	#[cfg(any(feature = "std", test))]
	pub fn set_parent_hash(n: T::Hash) {
		<ParentHash<T>>::put(n);
	}

	/// Set the current block weight. This should only be used in some integration tests.
	#[cfg(any(feature = "std", test))]
	pub fn set_block_limits(weight: Weight, len: usize) {
		AllExtrinsicsWeight::mutate(|current_weight| {
			current_weight.put(weight, DispatchClass::Normal)
		});
		AllExtrinsicsLen::put(len as u32);
	}

	/// Return the chain's current runtime version.
	pub fn runtime_version() -> RuntimeVersion { T::Version::get() }

	/// Retrieve the account transaction counter from storage.
	pub fn account_nonce(who: impl EncodeLike<T::AccountId>) -> T::Index {
		Account::<T>::get(who).nonce
	}

	/// Increment a particular account's nonce by 1.
	pub fn inc_account_nonce(who: impl EncodeLike<T::AccountId>) {
		Account::<T>::mutate(who, |a| a.nonce += T::Index::one());
	}

	/// Note what the extrinsic data of the current extrinsic index is. If this
	/// is called, then ensure `derive_extrinsics` is also called before
	/// block-building is completed.
	///
	/// NOTE: This function is called only when the block is being constructed locally.
	/// `execute_block` doesn't note any extrinsics.
	pub fn note_extrinsic(encoded_xt: Vec<u8>) {
		ExtrinsicData::insert(Self::extrinsic_index().unwrap_or_default(), encoded_xt);
	}

	/// To be called immediately after an extrinsic has been applied.
	pub fn note_applied_extrinsic(r: &DispatchOutcome, _encoded_len: u32, info: DispatchInfo) {
		Self::deposit_event(
			match r {
				Ok(()) => RawEvent::ExtrinsicSuccess(info),
				Err(err) => {
					sp_runtime::print(err);
					RawEvent::ExtrinsicFailed(err.clone(), info)
				},
			}
		);

		let next_extrinsic_index = Self::extrinsic_index().unwrap_or_default() + 1u32;

		storage::unhashed::put(well_known_keys::EXTRINSIC_INDEX, &next_extrinsic_index);
		ExecutionPhase::put(Phase::ApplyExtrinsic(next_extrinsic_index));
	}

	/// To be called immediately after `note_applied_extrinsic` of the last extrinsic of the block
	/// has been called.
	pub fn note_finished_extrinsics() {
		let extrinsic_index: u32 = storage::unhashed::take(well_known_keys::EXTRINSIC_INDEX)
			.unwrap_or_default();
		ExtrinsicCount::put(extrinsic_index);
		ExecutionPhase::put(Phase::Finalization);
	}

	/// To be called immediately after finishing the initialization of the block
	/// (e.g., called `on_initialize` for all modules).
	pub fn note_finished_initialize() {
		ExecutionPhase::put(Phase::ApplyExtrinsic(0))
	}

	/// Remove all extrinsic data and save the extrinsics trie root.
	pub fn derive_extrinsics() {
		let extrinsics = (0..ExtrinsicCount::get().unwrap_or_default())
			.map(ExtrinsicData::take).collect();
		let xts_root = extrinsics_data_root::<T::Hashing>(extrinsics);
		<ExtrinsicsRoot<T>>::put(xts_root);
	}

	/// An account is being created.
	pub fn on_created_account(who: T::AccountId) {
		T::OnNewAccount::on_new_account(&who);
		Self::deposit_event(RawEvent::NewAccount(who));
	}

	/// Do anything that needs to be done after an account has been killed.
	fn on_killed_account(who: T::AccountId) {
		T::OnKilledAccount::on_killed_account(&who);
		Self::deposit_event(RawEvent::KilledAccount(who));
	}

	/// Remove an account from storage. This should only be done when its refs are zero or you'll
	/// get storage leaks in other modules. Nonetheless we assume that the calling logic knows best.
	///
	/// This is a no-op if the account doesn't already exist. If it does then it will ensure
	/// cleanups (those in `on_killed_account`) take place.
	fn kill_account(who: &T::AccountId) {
		if Account::<T>::contains_key(who) {
			let account = Account::<T>::take(who);
			if account.refcount > 0 {
				debug::debug!(
					target: "system",
					"WARNING: Referenced account deleted. This is probably a bug."
				);
			}
			Module::<T>::on_killed_account(who.clone());
		}
	}

	/// Determine whether or not it is possible to update the code.
	///
	/// This function has no side effects and is idempotent, but is fairly
	/// heavy. It is automatically called by `set_code`; in most cases,
	/// a direct call to `set_code` is preferable. It is useful to call
	/// `can_set_code` when it is desirable to perform the appropriate
	/// runtime checks without actually changing the code yet.
	pub fn can_set_code(origin: T::Origin, code: &[u8]) -> Result<(), sp_runtime::DispatchError> {
		ensure_root(origin)?;

		let current_version = T::Version::get();
		let new_version = sp_io::misc::runtime_version(&code)
			.and_then(|v| RuntimeVersion::decode(&mut &v[..]).ok())
			.ok_or_else(|| Error::<T>::FailedToExtractRuntimeVersion)?;

		if new_version.spec_name != current_version.spec_name {
			Err(Error::<T>::InvalidSpecName)?
		}

		if new_version.spec_version <= current_version.spec_version {
			Err(Error::<T>::SpecVersionNeedsToIncrease)?
		}

		Ok(())
	}
}

/// Event handler which calls on_created_account when it happens.
pub struct CallOnCreatedAccount<T>(PhantomData<T>);
impl<T: Trait> Happened<T::AccountId> for CallOnCreatedAccount<T> {
	fn happened(who: &T::AccountId) {
		Module::<T>::on_created_account(who.clone());
	}
}

/// Event handler which calls kill_account when it happens.
pub struct CallKillAccount<T>(PhantomData<T>);
impl<T: Trait> Happened<T::AccountId> for CallKillAccount<T> {
	fn happened(who: &T::AccountId) {
		Module::<T>::kill_account(who)
	}
}

// Implement StoredMap for a simple single-item, kill-account-on-remove system. This works fine for
// storing a single item which is required to not be empty/default for the account to exist.
// Anything more complex will need more sophisticated logic.
impl<T: Trait> StoredMap<T::AccountId, T::AccountData> for Module<T> {
	fn get(k: &T::AccountId) -> T::AccountData {
		Account::<T>::get(k).data
	}
	fn is_explicit(k: &T::AccountId) -> bool {
		Account::<T>::contains_key(k)
	}
	fn insert(k: &T::AccountId, data: T::AccountData) {
		let existed = Account::<T>::contains_key(k);
		Account::<T>::mutate(k, |a| a.data = data);
		if !existed {
			Self::on_created_account(k.clone());
		}
	}
	fn remove(k: &T::AccountId) {
		Self::kill_account(k)
	}
	fn mutate<R>(k: &T::AccountId, f: impl FnOnce(&mut T::AccountData) -> R) -> R {
		let existed = Account::<T>::contains_key(k);
		let r = Account::<T>::mutate(k, |a| f(&mut a.data));
		if !existed {
			Self::on_created_account(k.clone());
		}
		r
	}
	fn mutate_exists<R>(k: &T::AccountId, f: impl FnOnce(&mut Option<T::AccountData>) -> R) -> R {
		Self::try_mutate_exists(k, |x| -> Result<R, Infallible> { Ok(f(x)) }).expect("Infallible; qed")
	}
	fn try_mutate_exists<R, E>(k: &T::AccountId, f: impl FnOnce(&mut Option<T::AccountData>) -> Result<R, E>) -> Result<R, E> {
		Account::<T>::try_mutate_exists(k, |maybe_value| {
			let existed = maybe_value.is_some();
			let (maybe_prefix, mut maybe_data) = split_inner(
				maybe_value.take(),
				|account| ((account.nonce, account.refcount), account.data)
			);
			f(&mut maybe_data).map(|result| {
				*maybe_value = maybe_data.map(|data| {
					let (nonce, refcount) = maybe_prefix.unwrap_or_default();
					AccountInfo { nonce, refcount, data }
				});
				(existed, maybe_value.is_some(), result)
			})
		}).map(|(existed, exists, v)| {
			if !existed && exists {
				Self::on_created_account(k.clone());
			} else if existed && !exists {
				Self::on_killed_account(k.clone());
			}
			v
		})
	}
}

/// Split an `option` into two constituent options, as defined by a `splitter` function.
pub fn split_inner<T, R, S>(option: Option<T>, splitter: impl FnOnce(T) -> (R, S))
	-> (Option<R>, Option<S>)
{
	match option {
		Some(inner) => {
			let (r, s) = splitter(inner);
			(Some(r), Some(s))
		}
		None => (None, None),
	}
}

/// resource limit check.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckWeight<T: Trait + Send + Sync>(PhantomData<T>);

impl<T: Trait + Send + Sync> CheckWeight<T> where
	T::Call: Dispatchable<Info=DispatchInfo, PostInfo=PostDispatchInfo>
{
	/// Get the quota ratio of each dispatch class type. This indicates that all operational and mandatory
	/// dispatches can use the full capacity of any resource, while user-triggered ones can consume
	/// a portion.
	fn get_dispatch_limit_ratio(class: DispatchClass) -> Perbill {
		match class {
			DispatchClass::Operational | DispatchClass::Mandatory
				=> <Perbill as sp_runtime::PerThing>::one(),
			DispatchClass::Normal => T::AvailableBlockRatio::get(),
		}
	}

	/// Checks if the current extrinsic can fit into the block with respect to block weight limits.
	///
	/// Upon successes, it returns the new block weight as a `Result`.
	fn check_weight(
		info: &DispatchInfoOf<T::Call>,
	) -> Result<ExtrinsicsWeight, TransactionValidityError> {
		let maximum_weight = T::MaximumBlockWeight::get();
		let mut all_weight = Module::<T>::all_extrinsics_weight();
		match info.class {
			// If we have a dispatch that must be included in the block, it ignores all the limits.
			DispatchClass::Mandatory => {
				let extrinsic_weight = info.weight.saturating_add(T::ExtrinsicBaseWeight::get());
				all_weight.add(extrinsic_weight, DispatchClass::Mandatory);
				Ok(all_weight)
			},
			// If we have a normal dispatch, we follow all the normal rules and limits.
			DispatchClass::Normal => {
				let normal_limit = Self::get_dispatch_limit_ratio(DispatchClass::Normal) * maximum_weight;
				let extrinsic_weight = info.weight.checked_add(T::ExtrinsicBaseWeight::get())
					.ok_or(InvalidTransaction::ExhaustsResources)?;
				all_weight.checked_add(extrinsic_weight, DispatchClass::Normal)
					.map_err(|_| InvalidTransaction::ExhaustsResources)?;
				if all_weight.get(DispatchClass::Normal) > normal_limit {
					Err(InvalidTransaction::ExhaustsResources.into())
				} else {
					Ok(all_weight)
				}
			},
			// If we have an operational dispatch, allow it if we have not used our full
			// "operational space" (independent of existing fullness).
			DispatchClass::Operational => {
				let operational_limit = Self::get_dispatch_limit_ratio(DispatchClass::Operational) * maximum_weight;
				let normal_limit = Self::get_dispatch_limit_ratio(DispatchClass::Normal) * maximum_weight;
				let operational_space = operational_limit.saturating_sub(normal_limit);

				let extrinsic_weight = info.weight.checked_add(T::ExtrinsicBaseWeight::get())
					.ok_or(InvalidTransaction::ExhaustsResources)?;
				all_weight.checked_add(extrinsic_weight, DispatchClass::Operational)
					.map_err(|_| InvalidTransaction::ExhaustsResources)?;

				// If it would fit in normally, its okay
				if all_weight.total() <= maximum_weight ||
				// If we have not used our operational space
				all_weight.get(DispatchClass::Operational) <= operational_space {
					Ok(all_weight)
				} else {
					Err(InvalidTransaction::ExhaustsResources.into())
				}
			}
		}
	}

	/// Checks if the current extrinsic can fit into the block with respect to block length limits.
	///
	/// Upon successes, it returns the new block length as a `Result`.
	fn check_block_length(
		info: &DispatchInfoOf<T::Call>,
		len: usize,
	) -> Result<u32, TransactionValidityError> {
		let current_len = Module::<T>::all_extrinsics_len();
		let maximum_len = T::MaximumBlockLength::get();
		let limit = Self::get_dispatch_limit_ratio(info.class) * maximum_len;
		let added_len = len as u32;
		let next_len = current_len.saturating_add(added_len);
		if next_len > limit {
			Err(InvalidTransaction::ExhaustsResources.into())
		} else {
			Ok(next_len)
		}
	}

	/// get the priority of an extrinsic denoted by `info`.
	fn get_priority(info: &DispatchInfoOf<T::Call>) -> TransactionPriority {
		match info.class {
			DispatchClass::Normal => info.weight.into(),
			DispatchClass::Operational => Bounded::max_value(),
			// Mandatory extrinsics are only for inherents; never transactions.
			DispatchClass::Mandatory => Bounded::min_value(),
		}
	}

	/// Creates new `SignedExtension` to check weight of the extrinsic.
	pub fn new() -> Self {
		Self(PhantomData)
	}

	/// Do the pre-dispatch checks. This can be applied to both signed and unsigned.
	///
	/// It checks and notes the new weight and length.
	fn do_pre_dispatch(
		info: &DispatchInfoOf<T::Call>,
		len: usize,
	) -> Result<(), TransactionValidityError> {
		let next_len = Self::check_block_length(info, len)?;
		let next_weight = Self::check_weight(info)?;
		AllExtrinsicsLen::put(next_len);
		AllExtrinsicsWeight::put(next_weight);
		Ok(())
	}

	/// Do the validate checks. This can be applied to both signed and unsigned.
	///
	/// It only checks that the block weight and length limit will not exceed.
	fn do_validate(
		info: &DispatchInfoOf<T::Call>,
		len: usize,
	) -> TransactionValidity {
		// ignore the next weight and length. If they return `Ok`, then it is below the limit.
		let _ = Self::check_block_length(info, len)?;
		let _ = Self::check_weight(info)?;

		Ok(ValidTransaction { priority: Self::get_priority(info), ..Default::default() })
	}
}

impl<T: Trait + Send + Sync> SignedExtension for CheckWeight<T> where
	T::Call: Dispatchable<Info=DispatchInfo, PostInfo=PostDispatchInfo>
{
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type Pre = ();
	const IDENTIFIER: &'static str = "CheckWeight";

	fn additional_signed(&self) -> sp_std::result::Result<(), TransactionValidityError> { Ok(()) }

	fn pre_dispatch(
		self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<(), TransactionValidityError> {
		if info.class == DispatchClass::Mandatory {
			Err(InvalidTransaction::MandatoryDispatch)?
		}
		Self::do_pre_dispatch(info, len)
	}

	fn validate(
		&self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		if info.class == DispatchClass::Mandatory {
			Err(InvalidTransaction::MandatoryDispatch)?
		}
		Self::do_validate(info, len)
	}

	fn pre_dispatch_unsigned(
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> Result<(), TransactionValidityError> {
		Self::do_pre_dispatch(info, len)
	}

	fn validate_unsigned(
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		len: usize,
	) -> TransactionValidity {
		Self::do_validate(info, len)
	}

	fn post_dispatch(
		_pre: Self::Pre,
		info: &DispatchInfoOf<Self::Call>,
		post_info: &PostDispatchInfoOf<Self::Call>,
		_len: usize,
		result: &DispatchResult,
	) -> Result<(), TransactionValidityError> {
		// Since mandatory dispatched do not get validated for being overweight, we are sensitive
		// to them actually being useful. Block producers are thus not allowed to include mandatory
		// extrinsics that result in error.
		if info.class == DispatchClass::Mandatory && result.is_err() {
			Err(InvalidTransaction::BadMandatory)?
		}

		let unspent = post_info.calc_unspent(info);
		if unspent > 0 {
			AllExtrinsicsWeight::mutate(|current_weight| {
				current_weight.sub(unspent, info.class);
			})
		}

		Ok(())
	}
}

impl<T: Trait + Send + Sync> Debug for CheckWeight<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "CheckWeight")
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

/// Nonce check and increment to give replay protection for transactions.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckNonce<T: Trait>(#[codec(compact)] T::Index);

impl<T: Trait> CheckNonce<T> {
	/// utility constructor. Used only in client/factory code.
	pub fn from(nonce: T::Index) -> Self {
		Self(nonce)
	}
}

impl<T: Trait> Debug for CheckNonce<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "CheckNonce({})", self.0)
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<T: Trait> SignedExtension for CheckNonce<T> where
	T::Call: Dispatchable<Info=DispatchInfo>
{
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type Pre = ();
	const IDENTIFIER: &'static str = "CheckNonce";

	fn additional_signed(&self) -> sp_std::result::Result<(), TransactionValidityError> { Ok(()) }

	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		_call: &Self::Call,
		_info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> Result<(), TransactionValidityError> {
		let mut account = Account::<T>::get(who);
		if self.0 != account.nonce {
			return Err(
				if self.0 < account.nonce {
					InvalidTransaction::Stale
				} else {
					InvalidTransaction::Future
				}.into()
			)
		}
		account.nonce += T::Index::one();
		Account::<T>::insert(who, account);
		Ok(())
	}

	fn validate(
		&self,
		who: &Self::AccountId,
		_call: &Self::Call,
		info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> TransactionValidity {
		// check index
		let account = Account::<T>::get(who);
		if self.0 < account.nonce {
			return InvalidTransaction::Stale.into()
		}

		let provides = vec![Encode::encode(&(who, self.0))];
		let requires = if account.nonce < self.0 {
			vec![Encode::encode(&(who, self.0 - One::one()))]
		} else {
			vec![]
		};

		Ok(ValidTransaction {
			priority: info.weight as TransactionPriority,
			requires,
			provides,
			longevity: TransactionLongevity::max_value(),
			propagate: true,
		})
	}
}

impl<T: Trait> IsDeadAccount<T::AccountId> for Module<T> {
	fn is_dead_account(who: &T::AccountId) -> bool {
		!Account::<T>::contains_key(who)
	}
}

/// Check for transaction mortality.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckEra<T: Trait + Send + Sync>(Era, sp_std::marker::PhantomData<T>);

impl<T: Trait + Send + Sync> CheckEra<T> {
	/// utility constructor. Used only in client/factory code.
	pub fn from(era: Era) -> Self {
		Self(era, sp_std::marker::PhantomData)
	}
}

impl<T: Trait + Send + Sync> Debug for CheckEra<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "CheckEra({:?})", self.0)
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<T: Trait + Send + Sync> SignedExtension for CheckEra<T> {
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = T::Hash;
	type Pre = ();
	const IDENTIFIER: &'static str = "CheckEra";

	fn validate(
		&self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		_info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> TransactionValidity {
		let current_u64 = <Module<T>>::block_number().saturated_into::<u64>();
		let valid_till = self.0.death(current_u64);
		Ok(ValidTransaction {
			longevity: valid_till.saturating_sub(current_u64),
			..Default::default()
		})
	}

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
		let current_u64 = <Module<T>>::block_number().saturated_into::<u64>();
		let n = self.0.birth(current_u64).saturated_into::<T::BlockNumber>();
		if !<BlockHash<T>>::contains_key(n) {
			Err(InvalidTransaction::AncientBirthBlock.into())
		} else {
			Ok(<Module<T>>::block_hash(n))
		}
	}
}

/// Nonce check and increment to give replay protection for transactions.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckGenesis<T: Trait + Send + Sync>(sp_std::marker::PhantomData<T>);

impl<T: Trait + Send + Sync> Debug for CheckGenesis<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "CheckGenesis")
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<T: Trait + Send + Sync> CheckGenesis<T> {
	/// Creates new `SignedExtension` to check genesis hash.
	pub fn new() -> Self {
		Self(sp_std::marker::PhantomData)
	}
}

impl<T: Trait + Send + Sync> SignedExtension for CheckGenesis<T> {
	type AccountId = T::AccountId;
	type Call = <T as Trait>::Call;
	type AdditionalSigned = T::Hash;
	type Pre = ();
	const IDENTIFIER: &'static str = "CheckGenesis";

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
		Ok(<Module<T>>::block_hash(T::BlockNumber::zero()))
	}
}

/// Ensure the runtime version registered in the transaction is the same as at present.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckVersion<T: Trait + Send + Sync>(sp_std::marker::PhantomData<T>);

impl<T: Trait + Send + Sync> Debug for CheckVersion<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "CheckVersion")
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<T: Trait + Send + Sync> CheckVersion<T> {
	/// Create new `SignedExtension` to check runtime version.
	pub fn new() -> Self {
		Self(sp_std::marker::PhantomData)
	}
}

impl<T: Trait + Send + Sync> SignedExtension for CheckVersion<T> {
	type AccountId = T::AccountId;
	type Call = <T as Trait>::Call;
	type AdditionalSigned = u32;
	type Pre = ();
	const IDENTIFIER: &'static str = "CheckVersion";

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
		Ok(<Module<T>>::runtime_version().spec_version)
	}
}

pub struct ChainContext<T>(sp_std::marker::PhantomData<T>);
impl<T> Default for ChainContext<T> {
	fn default() -> Self {
		ChainContext(sp_std::marker::PhantomData)
	}
}

impl<T: Trait> Lookup for ChainContext<T> {
	type Source = <T::Lookup as StaticLookup>::Source;
	type Target = <T::Lookup as StaticLookup>::Target;

	fn lookup(&self, s: Self::Source) -> Result<Self::Target, LookupError> {
		<T::Lookup as StaticLookup>::lookup(s)
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use super::*;
	use sp_std::cell::RefCell;
	use sp_core::H256;
	use sp_runtime::{traits::{BlakeTwo256, IdentityLookup, SignedExtension}, testing::Header, DispatchError};
	use frame_support::{impl_outer_origin, parameter_types, assert_ok, assert_noop};

	impl_outer_origin! {
		pub enum Origin for Test where system = super {}
	}

	#[derive(Clone, Eq, PartialEq, Debug)]
	pub struct Test;

	parameter_types! {
		pub const BlockHashCount: u64 = 10;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);
		pub const MaximumBlockLength: u32 = 1024;
		pub const Version: RuntimeVersion = RuntimeVersion {
			spec_name: sp_version::create_runtime_str!("test"),
			impl_name: sp_version::create_runtime_str!("system-test"),
			authoring_version: 1,
			spec_version: 1,
			impl_version: 1,
			apis: sp_version::create_apis_vec!([]),
			transaction_version: 1,
		};
		pub const BlockExecutionWeight: Weight = 10;
		pub const ExtrinsicBaseWeight: Weight = 5;
		pub const DbWeight: RuntimeDbWeight = RuntimeDbWeight {
			read: 10,
			write: 100,
		};
	}

	thread_local!{
		pub static KILLED: RefCell<Vec<u64>> = RefCell::new(vec![]);
	}

	pub struct RecordKilled;
	impl OnKilledAccount<u64> for RecordKilled {
		fn on_killed_account(who: &u64) { KILLED.with(|r| r.borrow_mut().push(*who)) }
	}

	#[derive(Debug, codec::Encode, codec::Decode)]
	pub struct Call;

	impl Dispatchable for Call {
		type Origin = ();
		type Trait = ();
		type Info = DispatchInfo;
		type PostInfo = PostDispatchInfo;
		fn dispatch(self, _origin: Self::Origin)
			-> sp_runtime::DispatchResultWithInfo<Self::PostInfo> {
				panic!("Do not use dummy implementation for dispatch.");
		}
	}

	impl Trait for Test {
		type Origin = Origin;
		type Call = Call;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = u16;
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type DbWeight = DbWeight;
		type BlockExecutionWeight = BlockExecutionWeight;
		type ExtrinsicBaseWeight = ExtrinsicBaseWeight;
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = Version;
		type ModuleToIndex = ();
		type AccountData = u32;
		type OnNewAccount = ();
		type OnKilledAccount = RecordKilled;
	}

	impl From<Event<Test>> for u16 {
		fn from(e: Event<Test>) -> u16 {
			match e {
				Event::<Test>::ExtrinsicSuccess(..) => 100,
				Event::<Test>::ExtrinsicFailed(..) => 101,
				Event::<Test>::CodeUpdated => 102,
				_ => 103,
			}
		}
	}

	type System = Module<Test>;

	const CALL: &<Test as Trait>::Call = &Call;

	fn new_test_ext() -> sp_io::TestExternalities {
		let mut ext: sp_io::TestExternalities = GenesisConfig::default().build_storage::<Test>().unwrap().into();
		// Add to each test the initial weight of a block
		ext.execute_with(|| System::register_extra_weight_unchecked(<Test as Trait>::BlockExecutionWeight::get(), DispatchClass::Mandatory));
		ext
	}

	fn normal_weight_limit() -> Weight {
		<Test as Trait>::AvailableBlockRatio::get() * <Test as Trait>::MaximumBlockWeight::get()
	}

	fn normal_length_limit() -> u32 {
		<Test as Trait>::AvailableBlockRatio::get() * <Test as Trait>::MaximumBlockLength::get()
	}

	#[test]
	fn origin_works() {
		let o = Origin::from(RawOrigin::<u64>::Signed(1u64));
		let x: Result<RawOrigin<u64>, Origin> = o.into();
		assert_eq!(x, Ok(RawOrigin::<u64>::Signed(1u64)));
	}

	#[test]
	fn stored_map_works() {
		new_test_ext().execute_with(|| {
			System::insert(&0, 42);
			assert!(System::allow_death(&0));

			System::inc_ref(&0);
			assert!(!System::allow_death(&0));

			System::insert(&0, 69);
			assert!(!System::allow_death(&0));

			System::dec_ref(&0);
			assert!(System::allow_death(&0));

			assert!(KILLED.with(|r| r.borrow().is_empty()));
			System::kill_account(&0);
			assert_eq!(KILLED.with(|r| r.borrow().clone()), vec![0u64]);
		});
	}

	#[test]
	fn deposit_event_should_work() {
		new_test_ext().execute_with(|| {
			System::initialize(
				&1,
				&[0u8; 32].into(),
				&[0u8; 32].into(),
				&Default::default(),
				InitKind::Full,
			);
			System::note_finished_extrinsics();
			System::deposit_event(1u16);
			System::finalize();
			assert_eq!(
				System::events(),
				vec![
					EventRecord {
						phase: Phase::Finalization,
						event: 1u16,
						topics: vec![],
					}
				]
			);

			System::initialize(
				&2,
				&[0u8; 32].into(),
				&[0u8; 32].into(),
				&Default::default(),
				InitKind::Full,
			);
			System::deposit_event(32u16);
			System::note_finished_initialize();
			System::deposit_event(42u16);
			System::note_applied_extrinsic(&Ok(()), 0, Default::default());
			System::note_applied_extrinsic(&Err(DispatchError::BadOrigin), 0, Default::default());
			System::note_finished_extrinsics();
			System::deposit_event(3u16);
			System::finalize();
			assert_eq!(
				System::events(),
				vec![
					EventRecord { phase: Phase::Initialization, event: 32u16, topics: vec![] },
					EventRecord { phase: Phase::ApplyExtrinsic(0), event: 42u16, topics: vec![] },
					EventRecord { phase: Phase::ApplyExtrinsic(0), event: 100u16, topics: vec![] },
					EventRecord { phase: Phase::ApplyExtrinsic(1), event: 101u16, topics: vec![] },
					EventRecord { phase: Phase::Finalization, event: 3u16, topics: vec![] }
				]
			);
		});
	}

	#[test]
	fn deposit_event_topics() {
		new_test_ext().execute_with(|| {
			const BLOCK_NUMBER: u64 = 1;

			System::initialize(
				&BLOCK_NUMBER,
				&[0u8; 32].into(),
				&[0u8; 32].into(),
				&Default::default(),
				InitKind::Full,
			);
			System::note_finished_extrinsics();

			let topics = vec![
				H256::repeat_byte(1),
				H256::repeat_byte(2),
				H256::repeat_byte(3),
			];

			// We deposit a few events with different sets of topics.
			System::deposit_event_indexed(&topics[0..3], 1u16);
			System::deposit_event_indexed(&topics[0..1], 2u16);
			System::deposit_event_indexed(&topics[1..2], 3u16);

			System::finalize();

			// Check that topics are reflected in the event record.
			assert_eq!(
				System::events(),
				vec![
					EventRecord {
						phase: Phase::Finalization,
						event: 1u16,
						topics: topics[0..3].to_vec(),
					},
					EventRecord {
						phase: Phase::Finalization,
						event: 2u16,
						topics: topics[0..1].to_vec(),
					},
					EventRecord {
						phase: Phase::Finalization,
						event: 3u16,
						topics: topics[1..2].to_vec(),
					}
				]
			);

			// Check that the topic-events mapping reflects the deposited topics.
			// Note that these are indexes of the events.
			assert_eq!(
				System::event_topics(&topics[0]),
				vec![(BLOCK_NUMBER, 0), (BLOCK_NUMBER, 1)],
			);
			assert_eq!(
				System::event_topics(&topics[1]),
				vec![(BLOCK_NUMBER, 0), (BLOCK_NUMBER, 2)],
			);
			assert_eq!(
				System::event_topics(&topics[2]),
				vec![(BLOCK_NUMBER, 0)],
			);
		});
	}

	#[test]
	fn prunes_block_hash_mappings() {
		new_test_ext().execute_with(|| {
			// simulate import of 15 blocks
			for n in 1..=15 {
				System::initialize(
					&n,
					&[n as u8 - 1; 32].into(),
					&[0u8; 32].into(),
					&Default::default(),
					InitKind::Full,
				);

				System::finalize();
			}

			// first 5 block hashes are pruned
			for n in 0..5 {
				assert_eq!(
					System::block_hash(n),
					H256::zero(),
				);
			}

			// the remaining 10 are kept
			for n in 5..15 {
				assert_eq!(
					System::block_hash(n),
					[n as u8; 32].into(),
				);
			}
		})
	}

	#[test]
	fn signed_ext_check_nonce_works() {
		new_test_ext().execute_with(|| {
			Account::<Test>::insert(1, AccountInfo { nonce: 1, refcount: 0, data: 0 });
			let info = DispatchInfo::default();
			let len = 0_usize;
			// stale
			assert!(CheckNonce::<Test>(0).validate(&1, CALL, &info, len).is_err());
			assert!(CheckNonce::<Test>(0).pre_dispatch(&1, CALL, &info, len).is_err());
			// correct
			assert!(CheckNonce::<Test>(1).validate(&1, CALL, &info, len).is_ok());
			assert!(CheckNonce::<Test>(1).pre_dispatch(&1, CALL, &info, len).is_ok());
			// future
			assert!(CheckNonce::<Test>(5).validate(&1, CALL, &info, len).is_ok());
			assert!(CheckNonce::<Test>(5).pre_dispatch(&1, CALL, &info, len).is_err());
		})
	}

	#[test]
	fn signed_ext_check_weight_works_normal_tx() {
		new_test_ext().execute_with(|| {
			let normal_limit = normal_weight_limit();
			let small = DispatchInfo { weight: 100, ..Default::default() };
			let medium = DispatchInfo {
				weight: normal_limit - <Test as Trait>::ExtrinsicBaseWeight::get(),
				..Default::default()
			};
			let big = DispatchInfo {
				weight: normal_limit - <Test as Trait>::ExtrinsicBaseWeight::get() + 1,
				..Default::default()
			};
			let len = 0_usize;

			let reset_check_weight = |i, f, s| {
				AllExtrinsicsWeight::mutate(|current_weight| {
					current_weight.put(s, DispatchClass::Normal)
				});
				let r = CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, i, len);
				if f { assert!(r.is_err()) } else { assert!(r.is_ok()) }
			};

			reset_check_weight(&small, false, 0);
			reset_check_weight(&medium, false, 0);
			reset_check_weight(&big, true, 1);
		})
	}

	#[test]
	fn signed_ext_check_weight_refund_works() {
		new_test_ext().execute_with(|| {
			// This is half of the max block weight
			let info = DispatchInfo { weight: 512, ..Default::default() };
			let post_info = PostDispatchInfo { actual_weight: Some(128), };
			let len = 0_usize;

			// We allow 75% for normal transaction, so we put 25% - extrinsic base weight
			AllExtrinsicsWeight::mutate(|current_weight| {
				current_weight.put(256 - <Test as Trait>::ExtrinsicBaseWeight::get(), DispatchClass::Normal)
			});

			let pre = CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, &info, len).unwrap();
			assert_eq!(AllExtrinsicsWeight::get().total(), info.weight + 256);

			assert!(
				CheckWeight::<Test>::post_dispatch(pre, &info, &post_info, len, &Ok(()))
				.is_ok()
			);
			assert_eq!(
				AllExtrinsicsWeight::get().total(),
				post_info.actual_weight.unwrap() + 256,
			);
		})
	}

	#[test]
	fn signed_ext_check_weight_actual_weight_higher_than_max_is_capped() {
		new_test_ext().execute_with(|| {
			let info = DispatchInfo { weight: 512, ..Default::default() };
			let post_info = PostDispatchInfo { actual_weight: Some(700), };
			let len = 0_usize;

			AllExtrinsicsWeight::mutate(|current_weight| {
				current_weight.put(128, DispatchClass::Normal)
			});

			let pre = CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, &info, len).unwrap();
			assert_eq!(
				AllExtrinsicsWeight::get().total(),
				info.weight + 128 + <Test as Trait>::ExtrinsicBaseWeight::get(),
			);

			assert!(
				CheckWeight::<Test>::post_dispatch(pre, &info, &post_info, len, &Ok(()))
				.is_ok()
			);
			assert_eq!(
				AllExtrinsicsWeight::get().total(),
				info.weight + 128 + <Test as Trait>::ExtrinsicBaseWeight::get(),
			);
		})
	}

	#[test]
	fn zero_weight_extrinsic_still_has_base_weight() {
		new_test_ext().execute_with(|| {
			let free = DispatchInfo { weight: 0, ..Default::default() };
			let len = 0_usize;

			// Initial weight from `BlockExecutionWeight`
			assert_eq!(System::all_extrinsics_weight().total(), <Test as Trait>::BlockExecutionWeight::get());
			let r = CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, &free, len);
			assert!(r.is_ok());
			assert_eq!(
				System::all_extrinsics_weight().total(),
				<Test as Trait>::ExtrinsicBaseWeight::get() + <Test as Trait>::BlockExecutionWeight::get()
			);
		})
	}

	#[test]
	fn mandatory_extrinsic_doesnt_care_about_limits() {
		new_test_ext().execute_with(|| {
			let max = DispatchInfo {
				weight: Weight::max_value(),
				class: DispatchClass::Mandatory,
				..Default::default()
			};
			let len = 0_usize;

			assert_ok!(CheckWeight::<Test>::do_pre_dispatch(&max, len));
			assert_eq!(System::all_extrinsics_weight().total(), Weight::max_value());
			assert!(System::all_extrinsics_weight().total() > <Test as Trait>::MaximumBlockWeight::get());
		});
	}

	#[test]
	fn register_extra_weight_unchecked_doesnt_care_about_limits() {
		new_test_ext().execute_with(|| {
			System::register_extra_weight_unchecked(Weight::max_value(), DispatchClass::Normal);
			assert_eq!(System::all_extrinsics_weight().total(), Weight::max_value());
			assert!(System::all_extrinsics_weight().total() > <Test as Trait>::MaximumBlockWeight::get());
		});
	}

	#[test]
	fn full_block_with_normal_and_operational() {
		new_test_ext().execute_with(|| {
			// Max block is 1024
			// Max normal is 768 (75%)
			// 10 is taken for block execution weight
			// So normal extrinsic can be 758 weight (-5 for base extrinsic weight)
			// And Operational can be 256 to produce a full block (-5 for base)
			let max_normal = DispatchInfo { weight: 753, ..Default::default() };
			let rest_operational = DispatchInfo { weight: 251, class: DispatchClass::Operational, ..Default::default() };

			let len = 0_usize;

			assert_ok!(CheckWeight::<Test>::do_pre_dispatch(&max_normal, len));
			assert_eq!(System::all_extrinsics_weight().total(), 768);
			assert_ok!(CheckWeight::<Test>::do_pre_dispatch(&rest_operational, len));
			assert_eq!(<Test as Trait>::MaximumBlockWeight::get(), 1024);
			assert_eq!(System::all_extrinsics_weight().total(), <Test as Trait>::MaximumBlockWeight::get());
		});
	}

	#[test]
	fn dispatch_order_does_not_effect_weight_logic() {
		new_test_ext().execute_with(|| {
			// We switch the order of `full_block_with_normal_and_operational`
			let max_normal = DispatchInfo { weight: 753, ..Default::default() };
			let rest_operational = DispatchInfo { weight: 251, class: DispatchClass::Operational, ..Default::default() };

			let len = 0_usize;

			assert_ok!(CheckWeight::<Test>::do_pre_dispatch(&rest_operational, len));
			// Extra 15 here from block execution + base extrinsic weight
			assert_eq!(System::all_extrinsics_weight().total(), 266);
			assert_ok!(CheckWeight::<Test>::do_pre_dispatch(&max_normal, len));
			assert_eq!(<Test as Trait>::MaximumBlockWeight::get(), 1024);
			assert_eq!(System::all_extrinsics_weight().total(), <Test as Trait>::MaximumBlockWeight::get());
		});
	}

	#[test]
	fn operational_works_on_full_block() {
		new_test_ext().execute_with(|| {
			// An on_initialize takes up the whole block! (Every time!)
			System::register_extra_weight_unchecked(Weight::max_value(), DispatchClass::Mandatory);
			let dispatch_normal = DispatchInfo { weight: 251, class: DispatchClass::Normal, ..Default::default() };
			let dispatch_operational = DispatchInfo { weight: 251, class: DispatchClass::Operational, ..Default::default() };
			let len = 0_usize;

			assert_noop!(CheckWeight::<Test>::do_pre_dispatch(&dispatch_normal, len), InvalidTransaction::ExhaustsResources);
			// Thank goodness we can still do an operational transaction to possibly save the blockchain.
			assert_ok!(CheckWeight::<Test>::do_pre_dispatch(&dispatch_operational, len));
			// Not too much though
			assert_noop!(CheckWeight::<Test>::do_pre_dispatch(&dispatch_operational, len), InvalidTransaction::ExhaustsResources);
		});
	}

	#[test]
	fn signed_ext_check_weight_works_operational_tx() {
		new_test_ext().execute_with(|| {
			let normal = DispatchInfo { weight: 100, ..Default::default() };
			let op = DispatchInfo { weight: 100, class: DispatchClass::Operational, pays_fee: Pays::Yes };
			let len = 0_usize;
			let normal_limit = normal_weight_limit();

			// given almost full block
			AllExtrinsicsWeight::mutate(|current_weight| {
				current_weight.put(normal_limit, DispatchClass::Normal)
			});
			// will not fit.
			assert!(CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, &normal, len).is_err());
			// will fit.
			assert!(CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, &op, len).is_ok());

			// likewise for length limit.
			let len = 100_usize;
			AllExtrinsicsLen::put(normal_length_limit());
			assert!(CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, &normal, len).is_err());
			assert!(CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, &op, len).is_ok());
		})
	}

	#[test]
	fn signed_ext_check_weight_priority_works() {
		new_test_ext().execute_with(|| {
			let normal = DispatchInfo { weight: 100, class: DispatchClass::Normal, pays_fee: Pays::Yes };
			let op = DispatchInfo { weight: 100, class: DispatchClass::Operational, pays_fee: Pays::Yes };
			let len = 0_usize;

			let priority = CheckWeight::<Test>(PhantomData)
				.validate(&1, CALL, &normal, len)
				.unwrap()
				.priority;
			assert_eq!(priority, 100);

			let priority = CheckWeight::<Test>(PhantomData)
				.validate(&1, CALL, &op, len)
				.unwrap()
				.priority;
			assert_eq!(priority, u64::max_value());
		})
	}

	#[test]
	fn signed_ext_check_weight_block_size_works() {
		new_test_ext().execute_with(|| {
			let normal = DispatchInfo::default();
			let normal_limit = normal_weight_limit() as usize;
			let reset_check_weight = |tx, s, f| {
				AllExtrinsicsLen::put(0);
				let r = CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, tx, s);
				if f { assert!(r.is_err()) } else { assert!(r.is_ok()) }
			};

			reset_check_weight(&normal, normal_limit - 1, false);
			reset_check_weight(&normal, normal_limit, false);
			reset_check_weight(&normal, normal_limit + 1, true);

			// Operational ones don't have this limit.
			let op = DispatchInfo { weight: 0, class: DispatchClass::Operational, pays_fee: Pays::Yes };
			reset_check_weight(&op, normal_limit, false);
			reset_check_weight(&op, normal_limit + 100, false);
			reset_check_weight(&op, 1024, false);
			reset_check_weight(&op, 1025, true);
		})
	}

	#[test]
	fn signed_ext_check_era_should_work() {
		new_test_ext().execute_with(|| {
			// future
			assert_eq!(
				CheckEra::<Test>::from(Era::mortal(4, 2)).additional_signed().err().unwrap(),
				InvalidTransaction::AncientBirthBlock.into(),
			);

			// correct
			System::set_block_number(13);
			<BlockHash<Test>>::insert(12, H256::repeat_byte(1));
			assert!(CheckEra::<Test>::from(Era::mortal(4, 12)).additional_signed().is_ok());
		})
	}

	#[test]
	fn signed_ext_check_era_should_change_longevity() {
		new_test_ext().execute_with(|| {
			let normal = DispatchInfo { weight: 100, class: DispatchClass::Normal, pays_fee: Pays::Yes };
			let len = 0_usize;
			let ext = (
				CheckWeight::<Test>(PhantomData),
				CheckEra::<Test>::from(Era::mortal(16, 256)),
			);
			System::set_block_number(17);
			<BlockHash<Test>>::insert(16, H256::repeat_byte(1));

			assert_eq!(ext.validate(&1, CALL, &normal, len).unwrap().longevity, 15);
		})
	}


	#[test]
	fn set_code_checks_works() {
		struct CallInWasm(Vec<u8>);

		impl sp_core::traits::CallInWasm for CallInWasm {
			fn call_in_wasm(
				&self,
				_: &[u8],
				_: Option<Vec<u8>>,
				_: &str,
				_: &[u8],
				_: &mut dyn sp_externalities::Externalities,
				_: sp_core::traits::MissingHostFunctions,
			) -> Result<Vec<u8>, String> {
				Ok(self.0.clone())
			}
		}

		let test_data = vec![
			("test", 1, 2, Err(Error::<Test>::SpecVersionNeedsToIncrease)),
			("test", 1, 1, Err(Error::<Test>::SpecVersionNeedsToIncrease)),
			("test2", 1, 1, Err(Error::<Test>::InvalidSpecName)),
			("test", 2, 1, Ok(())),
			("test", 0, 1, Err(Error::<Test>::SpecVersionNeedsToIncrease)),
			("test", 1, 0, Err(Error::<Test>::SpecVersionNeedsToIncrease)),
		];

		for (spec_name, spec_version, impl_version, expected) in test_data.into_iter() {
			let version = RuntimeVersion {
				spec_name: spec_name.into(),
				spec_version,
				impl_version,
				..Default::default()
			};
			let call_in_wasm = CallInWasm(version.encode());

			let mut ext = new_test_ext();
			ext.register_extension(sp_core::traits::CallInWasmExt::new(call_in_wasm));
			ext.execute_with(|| {
				let res = System::set_code(
					RawOrigin::Root.into(),
					vec![1, 2, 3, 4],
				);

				assert_eq!(expected.map_err(DispatchError::from), res);
			});
		}
	}

	#[test]
	fn set_code_with_real_wasm_blob() {
		let executor = substrate_test_runtime_client::new_native_executor();
		let mut ext = new_test_ext();
		ext.register_extension(sp_core::traits::CallInWasmExt::new(executor));
		ext.execute_with(|| {
			System::set_block_number(1);
			System::set_code(
				RawOrigin::Root.into(),
				substrate_test_runtime_client::runtime::WASM_BINARY.to_vec(),
			).unwrap();

			assert_eq!(
				System::events(),
				vec![EventRecord { phase: Phase::Initialization, event: 102u16, topics: vec![] }],
			);
		});
	}

	#[test]
	fn runtime_upgraded_with_set_storage() {
		let executor = substrate_test_runtime_client::new_native_executor();
		let mut ext = new_test_ext();
		ext.register_extension(sp_core::traits::CallInWasmExt::new(executor));
		ext.execute_with(|| {
			System::set_storage(
				RawOrigin::Root.into(),
				vec![(
					well_known_keys::CODE.to_vec(),
					substrate_test_runtime_client::runtime::WASM_BINARY.to_vec()
				)],
			).unwrap();
		});
	}

	#[test]
	fn events_not_emitted_during_genesis() {
		new_test_ext().execute_with(|| {
			// Block Number is zero at genesis
			assert!(System::block_number().is_zero());
			System::on_created_account(Default::default());
			assert!(System::events().is_empty());
			// Events will be emitted starting on block 1
			System::set_block_number(1);
			System::on_created_account(Default::default());
			assert!(System::events().len() == 1);
		});
	}
}
