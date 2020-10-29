// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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
//!   - [`CheckSpecVersion`]: Checks that the runtime version is the same as the one used to sign the
//!     transaction.
//!   - [`CheckTxVersion`]: Checks that the transaction version is the same as the one used to sign the
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
	RuntimeDebug, Perbill, DispatchError, Either, generic,
	traits::{
		self, CheckEqual, AtLeast32Bit, Zero, Lookup, LookupError,
		SimpleBitOps, Hash, Member, MaybeDisplay, BadOrigin,
		MaybeSerialize, MaybeSerializeDeserialize, MaybeMallocSizeOf, StaticLookup, One, Bounded,
		Dispatchable, AtLeast32BitUnsigned
	},
	offchain::storage_lock::BlockNumberProvider,
};

use sp_core::{ChangesTrieConfiguration, storage::well_known_keys};
use frame_support::{
	decl_module, decl_event, decl_storage, decl_error, Parameter, ensure, debug,
	storage,
	traits::{
		Contains, Get, PalletInfo, OnNewAccount, OnKilledAccount, IsDeadAccount, Happened,
		StoredMap, EnsureOrigin, OriginTrait, Filter,
	},
	weights::{
		Weight, RuntimeDbWeight, DispatchInfo, DispatchClass,
		extract_actual_weight,
	},
	dispatch::DispatchResultWithPostInfo,
};
use codec::{Encode, Decode, FullCodec, EncodeLike};

#[cfg(any(feature = "std", test))]
use sp_io::TestExternalities;

pub mod offchain;
#[cfg(test)]
pub(crate) mod mock;

mod extensions;
mod weight;
pub mod weights;
#[cfg(test)]
mod tests;

pub use extensions::{
	check_mortality::CheckMortality, check_genesis::CheckGenesis, check_nonce::CheckNonce,
	check_spec_version::CheckSpecVersion, check_tx_version::CheckTxVersion,
	check_weight::CheckWeight,
};
// Backward compatible re-export.
pub use extensions::check_mortality::CheckMortality as CheckEra;
pub use weights::WeightInfo;

/// Compute the trie root of a list of extrinsics.
pub fn extrinsics_root<H: Hash, E: codec::Encode>(extrinsics: &[E]) -> H::Output {
	extrinsics_data_root::<H>(extrinsics.iter().map(codec::Encode::encode).collect())
}

/// Compute the trie root of a list of extrinsics.
pub fn extrinsics_data_root<H: Hash>(xts: Vec<Vec<u8>>) -> H::Output {
	H::ordered_trie_root(xts)
}

pub trait Trait: 'static + Eq + Clone {
	/// The basic call filter to use in Origin. All origins are built with this filter as base,
	/// except Root.
	type BaseCallFilter: Filter<Self::Call>;

	/// The `Origin` type used by dispatchable calls.
	type Origin:
		Into<Result<RawOrigin<Self::AccountId>, Self::Origin>>
		+ From<RawOrigin<Self::AccountId>>
		+ Clone
		+ OriginTrait<Call = Self::Call>;

	/// The aggregated `Call` type.
	type Call: Dispatchable + Debug;

	/// Account index (aka nonce) type. This stores the number of previous transactions associated
	/// with a sender account.
	type Index:
		Parameter + Member + MaybeSerialize + Debug + Default + MaybeDisplay + AtLeast32Bit
		+ Copy;

	/// The block number type used by the runtime.
	type BlockNumber:
		Parameter + Member + MaybeSerializeDeserialize + Debug + MaybeDisplay +
		AtLeast32BitUnsigned + Default + Bounded + Copy + sp_std::hash::Hash +
		sp_std::str::FromStr + MaybeMallocSizeOf;

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

	/// The maximal weight of a single Extrinsic. This should be set to at most
	/// `MaximumBlockWeight - AverageOnInitializeWeight`. The limit only applies to extrinsics
	/// containing `Normal` dispatch class calls.
	type MaximumExtrinsicWeight: Get<Weight>;

	/// The maximum length of a block (in bytes).
	type MaximumBlockLength: Get<u32>;

	/// The portion of the block that is available to normal transaction. The rest can only be used
	/// by operational transactions. This can be applied to any resource limit managed by the system
	/// module, including weight and length.
	type AvailableBlockRatio: Get<Perbill>;

	/// Get the chain's current version.
	type Version: Get<RuntimeVersion>;

	/// Provides information about the pallet setup in the runtime.
	///
	/// Expects the `PalletInfo` type that is being generated by `construct_runtime!` in the
	/// runtime.
	///
	/// For tests it is okay to use `()` as type, however it will provide "useless" data.
	type PalletInfo: PalletInfo;

	/// Data to be associated with an account (other than nonce/transaction counter, which this
	/// module does regardless).
	type AccountData: Member + FullCodec + Clone + Default;

	/// Handler for when a new account has just been created.
	type OnNewAccount: OnNewAccount<Self::AccountId>;

	/// A function that is invoked when an account has been determined to be dead.
	///
	/// All resources should be cleaned up associated with the given account.
	type OnKilledAccount: OnKilledAccount<Self::AccountId>;

	type SystemWeightInfo: WeightInfo;
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
#[derive(PartialEq, Eq, Clone, RuntimeDebug, Encode, Decode)]
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
pub type RefCount = u32;

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

decl_storage! {
	trait Store for Module<T: Trait> as System {
		/// The full account information for a particular account ID.
		pub Account get(fn account):
			map hasher(blake2_128_concat) T::AccountId => AccountInfo<T::Index, T::AccountData>;

		/// Total extrinsics count for the current block.
		ExtrinsicCount: Option<u32>;

		/// The current weight for the block.
		BlockWeight get(fn block_weight): weight::ExtrinsicsWeight;

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

		/// True if we have upgraded so that `type RefCount` is `u32`. False (default) if not.
		UpgradedToU32RefCount build(|_| true): bool;

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
		/// An extrinsic completed successfully. \[info\]
		ExtrinsicSuccess(DispatchInfo),
		/// An extrinsic failed. \[error, info\]
		ExtrinsicFailed(DispatchError, DispatchInfo),
		/// `:code` was updated.
		CodeUpdated,
		/// A new \[account\] was created.
		NewAccount(AccountId),
		/// An \[account\] was reaped.
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
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system=self {
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

		fn on_runtime_upgrade() -> frame_support::weights::Weight {
			if !UpgradedToU32RefCount::get() {
				Account::<T>::translate::<(T::Index, u8, T::AccountData), _>(|_key, (nonce, rc, data)|
					Some(AccountInfo { nonce, refcount: rc as RefCount, data })
				);
				UpgradedToU32RefCount::put(true);
				T::MaximumBlockWeight::get()
			} else {
				0
			}
		}

		/// A dispatch that will fill the block weight up to the given ratio.
		// TODO: This should only be available for testing, rather than in general usage, but
		// that's not possible at present (since it's within the decl_module macro).
		#[weight = *_ratio * T::MaximumBlockWeight::get()]
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
		#[weight = T::SystemWeightInfo::remark(_remark.len() as u32)]
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
		#[weight = (T::SystemWeightInfo::set_heap_pages(), DispatchClass::Operational)]
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
			ensure_root(origin)?;
			Self::can_set_code(&code)?;

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
		#[weight = (T::SystemWeightInfo::set_changes_trie_config(), DispatchClass::Operational)]
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
		#[weight = (
			T::SystemWeightInfo::set_storage(items.len() as u32),
			DispatchClass::Operational,
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
		#[weight = (
			T::SystemWeightInfo::kill_storage(keys.len() as u32),
			DispatchClass::Operational,
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
		#[weight = (
			T::SystemWeightInfo::kill_prefix(_subkeys.saturating_add(1)),
			DispatchClass::Operational,
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
		#[weight = (T::SystemWeightInfo::suicide(), DispatchClass::Operational)]
		pub fn suicide(origin) {
			let who = ensure_signed(origin)?;
			let account = Account::<T>::get(&who);
			ensure!(account.refcount == 0, Error::<T>::NonZeroRefCount);
			ensure!(account.data == T::AccountData::default(), Error::<T>::NonDefaultComposite);
			Self::kill_account(&who);
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

/// The "OR gate" implementation of `EnsureOrigin`.
///
/// Origin check will pass if `L` or `R` origin check passes. `L` is tested first.
pub struct EnsureOneOf<AccountId, L, R>(sp_std::marker::PhantomData<(AccountId, L, R)>);
impl<
	AccountId,
	O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
	L: EnsureOrigin<O>,
	R: EnsureOrigin<O>,
> EnsureOrigin<O> for EnsureOneOf<AccountId, L, R> {
	type Success = Either<L::Success, R::Success>;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		L::try_origin(o).map_or_else(
			|o| R::try_origin(o).map(|o| Either::Right(o)),
			|o| Ok(Either::Left(o)),
		)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		L::successful_origin()
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
		BlockWeight::mutate(|current_weight| {
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

		// Remove previous block data from storage
		BlockWeight::kill();

		// Kill inspectable storage entries in state when `InitKind::Full`.
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
		BlockWeight::mutate(|current_weight| {
			current_weight.put(weight, DispatchClass::Normal)
		});
		AllExtrinsicsLen::put(len as u32);
	}

	/// Reset events. Can be used as an alternative to
	/// `initialize` for tests that don't need to bother with the other environment entries.
	#[cfg(any(feature = "std", feature = "runtime-benchmarks", test))]
	pub fn reset_events() {
		<Events<T>>::kill();
		EventCount::kill();
		<EventTopics<T>>::remove_all();
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
	pub fn note_applied_extrinsic(r: &DispatchResultWithPostInfo, mut info: DispatchInfo) {
		info.weight = extract_actual_weight(r, &info);
		Self::deposit_event(
			match r {
				Ok(_) => RawEvent::ExtrinsicSuccess(info),
				Err(err) => {
					sp_runtime::print(err);
					RawEvent::ExtrinsicFailed(err.error, info)
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
		}
		Module::<T>::on_killed_account(who.clone());
	}

	/// Determine whether or not it is possible to update the code.
	///
	/// Checks the given code if it is a valid runtime wasm blob by instantianting
	/// it and extracting the runtime version of it. It checks that the runtime version
	/// of the old and new runtime has the same spec name and that the spec version is increasing.
	pub fn can_set_code(code: &[u8]) -> Result<(), sp_runtime::DispatchError> {
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

impl<T: Trait> BlockNumberProvider for Module<T>
{
	type BlockNumber = <T as Trait>::BlockNumber;

	fn current_block_number() -> Self::BlockNumber {
		Module::<T>::block_number()
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


impl<T: Trait> IsDeadAccount<T::AccountId> for Module<T> {
	fn is_dead_account(who: &T::AccountId) -> bool {
		!Account::<T>::contains_key(who)
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
