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
//! It acts as the base layer for other SRML modules to interact with the Substrate framework components.
//!
//! - [`system::Trait`](./trait.Trait.html)
//!
//! ## Overview
//!
//! The System module defines the core data types used in a Substrate runtime.
//! It also provides several utility functions (see [`Module`](./struct.Module.html)) for other runtime modules.
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
//! The system module defines the following extensions:
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
use sp_std::marker::PhantomData;
use sp_std::fmt::Debug;
use sp_version::RuntimeVersion;
use sp_runtime::{
	RuntimeDebug,
	generic::{self, Era}, Perbill, DispatchOutcome, DispatchError,
	transaction_validity::{
		ValidTransaction, TransactionPriority, TransactionLongevity, TransactionValidityError,
		InvalidTransaction, TransactionValidity,
	},
	traits::{
		self, CheckEqual, SimpleArithmetic, Zero, SignedExtension, Lookup, LookupError,
		SimpleBitOps, Hash, Member, MaybeDisplay, EnsureOrigin, BadOrigin, SaturatedConversion,
		MaybeSerialize, MaybeSerializeDeserialize, StaticLookup, One, Bounded,
	},
};

use sp_core::{ChangesTrieConfiguration, storage::well_known_keys};
use frame_support::{
	decl_module, decl_event, decl_storage, decl_error, storage, Parameter,
	traits::{Contains, Get, ModuleToIndex, OnReapAccount},
	weights::{Weight, DispatchInfo, DispatchClass, SimpleDispatchInfo},
};
use codec::{Encode, Decode};

#[cfg(any(feature = "std", test))]
use sp_io::TestExternalities;

pub mod offchain;

/// Handler for when a new account has been created.
#[impl_trait_for_tuples::impl_for_tuples(30)]
pub trait OnNewAccount<AccountId> {
	/// A new account `who` has been registered.
	fn on_new_account(who: &AccountId);
}

/// Determiner to say whether a given account is unused.
pub trait IsDeadAccount<AccountId> {
	/// Is the given account dead?
	fn is_dead_account(who: &AccountId) -> bool;
}

impl<AccountId> IsDeadAccount<AccountId> for () {
	fn is_dead_account(_who: &AccountId) -> bool {
		true
	}
}

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
	type Call: Debug;

	/// Account index (aka nonce) type. This stores the number of previous transactions associated
	/// with a sender account.
	type Index:
		Parameter + Member + MaybeSerialize + Debug + Default + MaybeDisplay + SimpleArithmetic
		+ Copy;

	/// The block number type used by the runtime.
	type BlockNumber:
		Parameter + Member + MaybeSerializeDeserialize + Debug + MaybeDisplay + SimpleArithmetic
		+ Default + Bounded + Copy + sp_std::hash::Hash + sp_std::str::FromStr;

	/// The output of the `Hashing` function.
	type Hash:
		Parameter + Member + MaybeSerializeDeserialize + Debug + MaybeDisplay + SimpleBitOps + Ord
		+ Default + Copy + CheckEqual + sp_std::hash::Hash + AsRef<[u8]> + AsMut<[u8]>;

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
	type Event: Parameter + Member + From<Event> + Debug;

	/// Maximum number of block number to block hash mappings to keep (oldest pruned first).
	type BlockHashCount: Get<Self::BlockNumber>;

	/// The maximum weight of a block.
	type MaximumBlockWeight: Get<Weight>;

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
}

pub type DigestOf<T> = generic::Digest<<T as Trait>::Hash>;
pub type DigestItemOf<T> = generic::DigestItem<<T as Trait>::Hash>;

pub type Key = Vec<u8>;
pub type KeyValue = (Vec<u8>, Vec<u8>);

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		/// A big dispatch that will disallow any other transaction to be included.
		// TODO: this must be preferable available for testing really (not possible at the moment).
		#[weight = SimpleDispatchInfo::MaxOperational]
		fn fill_block(origin) {
			ensure_root(origin)?;
		}

		/// Make some on-chain remark.
		#[weight = SimpleDispatchInfo::FixedNormal(10_000)]
		fn remark(origin, _remark: Vec<u8>) {
			ensure_signed(origin)?;
		}

		/// Set the number of pages in the WebAssembly environment's heap.
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn set_heap_pages(origin, pages: u64) {
			ensure_root(origin)?;
			storage::unhashed::put_raw(well_known_keys::HEAP_PAGES, &pages.encode());
		}

		/// Set the new runtime code.
		#[weight = SimpleDispatchInfo::FixedOperational(200_000)]
		pub fn set_code(origin, code: Vec<u8>) {
			ensure_root(origin)?;

			let current_version = T::Version::get();
			let new_version = sp_io::misc::runtime_version(&code)
				.and_then(|v| RuntimeVersion::decode(&mut &v[..]).ok())
				.ok_or_else(|| Error::<T>::FailedToExtractRuntimeVersion)?;

			if new_version.spec_name != current_version.spec_name {
				Err(Error::<T>::InvalidSpecName)?
			}

			if new_version.spec_version < current_version.spec_version {
				Err(Error::<T>::SpecVersionNotAllowedToDecrease)?
			} else if new_version.spec_version == current_version.spec_version {
				if new_version.impl_version < current_version.impl_version {
					Err(Error::<T>::ImplVersionNotAllowedToDecrease)?
				} else if new_version.impl_version == current_version.impl_version {
					Err(Error::<T>::SpecOrImplVersionNeedToIncrease)?
				}
			}

			storage::unhashed::put_raw(well_known_keys::CODE, &code);
			Self::deposit_event(Event::CodeUpdated);
		}

		/// Set the new runtime code without doing any checks of the given `code`.
		#[weight = SimpleDispatchInfo::FixedOperational(200_000)]
		pub fn set_code_without_checks(origin, code: Vec<u8>) {
			ensure_root(origin)?;
			storage::unhashed::put_raw(well_known_keys::CODE, &code);
			Self::deposit_event(Event::CodeUpdated);
		}

		/// Set the new changes trie configuration.
		#[weight = SimpleDispatchInfo::FixedOperational(20_000)]
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
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn set_storage(origin, items: Vec<KeyValue>) {
			ensure_root(origin)?;
			for i in &items {
				storage::unhashed::put_raw(&i.0, &i.1);
			}
		}

		/// Kill some items from storage.
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn kill_storage(origin, keys: Vec<Key>) {
			ensure_root(origin)?;
			for key in &keys {
				storage::unhashed::kill(&key);
			}
		}

		/// Kill all storage items with a key that starts with the given prefix.
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn kill_prefix(origin, prefix: Key) {
			ensure_root(origin)?;
			storage::unhashed::kill_prefix(&prefix);
		}
	}
}

/// A phase of a block's execution.
#[derive(Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, PartialEq, Eq, Clone))]
pub enum Phase {
	/// Applying an extrinsic.
	ApplyExtrinsic(u32),
	/// The end.
	Finalization,
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

decl_event!(
	/// Event for the System module.
	pub enum Event {
		/// An extrinsic completed successfully.
		ExtrinsicSuccess(DispatchInfo),
		/// An extrinsic failed.
		ExtrinsicFailed(DispatchError, DispatchInfo),
		/// `:code` was updated.
		CodeUpdated,
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
		SpecVersionNotAllowedToDecrease,
		/// The implementation version is not allowed to decrease between the current runtime
		/// and the new runtime.
		ImplVersionNotAllowedToDecrease,
		/// The specification or the implementation version need to increase between the
		/// current runtime and the new runtime.
		SpecOrImplVersionNeedToIncrease,
		/// Failed to extract the runtime version from the new runtime.
		///
		/// Either calling `Core_version` or decoding `RuntimeVersion` failed.
		FailedToExtractRuntimeVersion,
	}
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

decl_storage! {
	trait Store for Module<T: Trait> as System {
		/// Extrinsics nonce for accounts.
		pub AccountNonce get(fn account_nonce): map hasher(blake2_256) T::AccountId => T::Index;
		/// Total extrinsics count for the current block.
		ExtrinsicCount: Option<u32>;
		/// Total weight for all extrinsics put together, for the current block.
		AllExtrinsicsWeight: Option<Weight>;
		/// Total length (in bytes) for all extrinsics put together, for the current block.
		AllExtrinsicsLen: Option<u32>;
		/// Map of block numbers to block hashes.
		pub BlockHash get(fn block_hash) build(|_| vec![(T::BlockNumber::zero(), hash69())]):
			map hasher(blake2_256) T::BlockNumber => T::Hash;
		/// Extrinsics data for the current block (maps an extrinsic's index to its data).
		ExtrinsicData get(fn extrinsic_data): map hasher(blake2_256) u32 => Vec<u8>;
		/// The current block number being processed. Set by `execute_block`.
		Number get(fn block_number) build(|_| 1.into()): T::BlockNumber;
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
		EventTopics get(fn event_topics): map hasher(blake2_256) T::Hash => Vec<(T::BlockNumber, EventIndex)>;
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
}

pub struct EnsureSigned<AccountId>(sp_std::marker::PhantomData<AccountId>);
impl<
	O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
	AccountId,
> EnsureOrigin<O> for EnsureSigned<AccountId> {
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Signed(who) => Ok(who),
			r => Err(O::from(r)),
		})
	}
}

pub struct EnsureSignedBy<Who, AccountId>(sp_std::marker::PhantomData<(Who, AccountId)>);
impl<
	O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
	Who: Contains<AccountId>,
	AccountId: PartialEq + Clone + Ord,
> EnsureOrigin<O> for EnsureSignedBy<Who, AccountId> {
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Signed(ref who) if Who::contains(who) => Ok(who.clone()),
			r => Err(O::from(r)),
		})
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
}

pub struct EnsureNever<T>(sp_std::marker::PhantomData<T>);
impl<O, T> EnsureOrigin<O> for EnsureNever<T> {
	type Success = T;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		Err(o)
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

impl<T: Trait> Module<T> {
	/// Deposits an event into this block's event record.
	pub fn deposit_event(event: impl Into<T::Event>) {
		Self::deposit_event_indexed(&[], event.into());
	}

	/// Deposits an event into this block's event record adding this event
	/// to the corresponding topic indexes.
	///
	/// This will update storage entries that correspond to the specified topics.
	/// It is expected that light-clients could subscribe to this topics.
	pub fn deposit_event_indexed(topics: &[T::Hash], event: T::Event) {
		let extrinsic_index = Self::extrinsic_index();
		let phase = extrinsic_index.map_or(Phase::Finalization, |c| Phase::ApplyExtrinsic(c));
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

		// Appending can only fail if `Events<T>` can not be decoded or
		// when we try to insert more than `u32::max_value()` events.
		//
		// We perform early return if we've reached the maximum capacity of the event list,
		// so `Events<T>` seems to be corrupted. Also, this has happened after the start of execution
		// (since the event list is cleared at the block initialization).
		if <Events<T>>::append([event].iter()).is_err() {
			// The most sensible thing to do here is to just ignore this event and wait until the
			// new block.
			return;
		}

		let block_no = Self::block_number();
		for topic in topics {
			// The same applies here.
			if <EventTopics<T>>::append(topic, &[(block_no, event_idx)]).is_err() {
				return;
			}
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

	/// Gets a total weight of all executed extrinsics.
	pub fn all_extrinsics_weight() -> Weight {
		AllExtrinsicsWeight::get().unwrap_or_default()
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
	/// Another potential use-case could be for the `on_initialise` and `on_finalize` hooks.
	///
	/// If no previous weight exists, the function initializes the weight to zero.
	pub fn register_extra_weight_unchecked(weight: Weight) {
		let current_weight = AllExtrinsicsWeight::get().unwrap_or_default();
		let next_weight = current_weight.saturating_add(weight).min(T::MaximumBlockWeight::get());
		AllExtrinsicsWeight::put(next_weight);
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
	pub fn deposit_log(item: DigestItemOf<T>) {
		let mut l = <Digest<T>>::get();
		l.push(item);
		<Digest<T>>::put(l);
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
			children: map![],
		})
	}

	/// Set the block number to something in particular. Can be used as an alternative to
	/// `initialize` for tests that don't need to bother with the other environment entries.
	#[cfg(any(feature = "std", test))]
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
		AllExtrinsicsWeight::put(weight);
		AllExtrinsicsLen::put(len as u32);
	}

	/// Return the chain's current runtime version.
	pub fn runtime_version() -> RuntimeVersion { T::Version::get() }

	/// Increment a particular account's nonce by 1.
	pub fn inc_account_nonce(who: &T::AccountId) {
		<AccountNonce<T>>::insert(who, Self::account_nonce(who) + T::Index::one());
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
				Ok(()) => Event::ExtrinsicSuccess(info),
				Err(err) => {
					sp_runtime::print(err);
					Event::ExtrinsicFailed(err.clone(), info)
				},
			}
		);

		let next_extrinsic_index = Self::extrinsic_index().unwrap_or_default() + 1u32;

		storage::unhashed::put(well_known_keys::EXTRINSIC_INDEX, &next_extrinsic_index);
	}

	/// To be called immediately after `note_applied_extrinsic` of the last extrinsic of the block
	/// has been called.
	pub fn note_finished_extrinsics() {
		let extrinsic_index: u32 = storage::unhashed::take(well_known_keys::EXTRINSIC_INDEX)
			.unwrap_or_default();
		ExtrinsicCount::put(extrinsic_index);
	}

	/// Remove all extrinsic data and save the extrinsics trie root.
	pub fn derive_extrinsics() {
		let extrinsics = (0..ExtrinsicCount::get().unwrap_or_default())
			.map(ExtrinsicData::take).collect();
		let xts_root = extrinsics_data_root::<T::Hashing>(extrinsics);
		<ExtrinsicsRoot<T>>::put(xts_root);
	}
}

impl<T: Trait> OnReapAccount<T::AccountId> for Module<T> {
	/// Remove the nonce for the account. Account is considered fully removed from the system.
	fn on_reap_account(who: &T::AccountId) {
		<AccountNonce<T>>::remove(who);
	}
}

/// resource limit check.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckWeight<T: Trait + Send + Sync>(PhantomData<T>);

impl<T: Trait + Send + Sync> CheckWeight<T> {
	/// Get the quota ratio of each dispatch class type. This indicates that all operational
	/// dispatches can use the full capacity of any resource, while user-triggered ones can consume
	/// a portion.
	fn get_dispatch_limit_ratio(class: DispatchClass) -> Perbill {
		match class {
			DispatchClass::Operational => Perbill::one(),
			DispatchClass::Normal => T::AvailableBlockRatio::get(),
		}
	}

	/// Checks if the current extrinsic can fit into the block with respect to block weight limits.
	///
	/// Upon successes, it returns the new block weight as a `Result`.
	fn check_weight(
		info: <Self as SignedExtension>::DispatchInfo,
	) -> Result<Weight, TransactionValidityError> {
		let current_weight = Module::<T>::all_extrinsics_weight();
		let maximum_weight = T::MaximumBlockWeight::get();
		let limit = Self::get_dispatch_limit_ratio(info.class) * maximum_weight;
		let added_weight = info.weight.min(limit);
		let next_weight = current_weight.saturating_add(added_weight);
		if next_weight > limit {
			Err(InvalidTransaction::ExhaustsResources.into())
		} else {
			Ok(next_weight)
		}
	}

	/// Checks if the current extrinsic can fit into the block with respect to block length limits.
	///
	/// Upon successes, it returns the new block length as a `Result`.
	fn check_block_length(
		info: <Self as SignedExtension>::DispatchInfo,
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
	fn get_priority(info: <Self as SignedExtension>::DispatchInfo) -> TransactionPriority {
		match info.class {
			DispatchClass::Normal => info.weight.into(),
			DispatchClass::Operational => Bounded::max_value()
		}
	}

	/// Creates new `SignedExtension` to check weight of the extrinsic.
	pub fn new() -> Self {
		Self(PhantomData)
	}
}

impl<T: Trait + Send + Sync> SignedExtension for CheckWeight<T> {
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type DispatchInfo = DispatchInfo;
	type Pre = ();
	const IDENTIFIER: &'static str = "CheckWeight";

	fn additional_signed(&self) -> sp_std::result::Result<(), TransactionValidityError> { Ok(()) }

	fn pre_dispatch(
		self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		info: Self::DispatchInfo,
		len: usize,
	) -> Result<(), TransactionValidityError> {
		let next_len = Self::check_block_length(info, len)?;
		AllExtrinsicsLen::put(next_len);
		let next_weight = Self::check_weight(info)?;
		AllExtrinsicsWeight::put(next_weight);
		Ok(())
	}

	fn validate(
		&self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		info: Self::DispatchInfo,
		len: usize,
	) -> TransactionValidity {
		// There is no point in writing to storage here since changes are discarded. This basically
		// discards any transaction which is bigger than the length or weight limit **alone**, which
		// is a guarantee that it will fail in the pre-dispatch phase.
		if let Err(e) = Self::check_block_length(info, len) {
			return Err(e);
		}

		if let Err(e) = Self::check_weight(info) {
			return Err(e);
		}

		Ok(ValidTransaction { priority: Self::get_priority(info), ..Default::default() })
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
		self.0.fmt(f)
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<T: Trait> SignedExtension for CheckNonce<T> {
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type DispatchInfo = DispatchInfo;
	type Pre = ();
	const IDENTIFIER: &'static str = "CheckNonce";

	fn additional_signed(&self) -> sp_std::result::Result<(), TransactionValidityError> { Ok(()) }

	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		_call: &Self::Call,
		_info: Self::DispatchInfo,
		_len: usize,
	) -> Result<(), TransactionValidityError> {
		let expected = <AccountNonce<T>>::get(who);
		if self.0 != expected {
			return Err(
				if self.0 < expected {
					InvalidTransaction::Stale
				} else {
					InvalidTransaction::Future
				}.into()
			)
		}

		<AccountNonce<T>>::insert(who, expected + T::Index::one());
		Ok(())
	}

	fn validate(
		&self,
		who: &Self::AccountId,
		_call: &Self::Call,
		info: Self::DispatchInfo,
		_len: usize,
	) -> TransactionValidity {
		// check index
		let expected = <AccountNonce<T>>::get(who);
		if self.0 < expected {
			return InvalidTransaction::Stale.into()
		}

		let provides = vec![Encode::encode(&(who, self.0))];
		let requires = if expected < self.0 {
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

/// Check for transaction mortality.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckEra<T: Trait + Send + Sync>((Era, sp_std::marker::PhantomData<T>));

impl<T: Trait + Send + Sync> CheckEra<T> {
	/// utility constructor. Used only in client/factory code.
	pub fn from(era: Era) -> Self {
		Self((era, sp_std::marker::PhantomData))
	}
}

impl<T: Trait + Send + Sync> Debug for CheckEra<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		self.0.fmt(f)
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
	type DispatchInfo = DispatchInfo;
	type Pre = ();
	const IDENTIFIER: &'static str = "CheckEra";

	fn validate(
		&self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		_info: Self::DispatchInfo,
		_len: usize,
	) -> TransactionValidity {
		let current_u64 = <Module<T>>::block_number().saturated_into::<u64>();
		let valid_till = (self.0).0.death(current_u64);
		Ok(ValidTransaction {
			longevity: valid_till.saturating_sub(current_u64),
			..Default::default()
		})
	}

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
		let current_u64 = <Module<T>>::block_number().saturated_into::<u64>();
		let n = (self.0).0.birth(current_u64).saturated_into::<T::BlockNumber>();
		if !<BlockHash<T>>::exists(n) {
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
	type DispatchInfo = DispatchInfo;
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
	type DispatchInfo = DispatchInfo;
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
mod tests {
	use super::*;
	use sp_core::H256;
	use sp_runtime::{traits::{BlakeTwo256, IdentityLookup}, testing::Header, DispatchError};
	use frame_support::{impl_outer_origin, parameter_types};

	impl_outer_origin! {
		pub enum Origin for Test where system = super {}
	}

	#[derive(Clone, Eq, PartialEq)]
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
		};
	}

	impl Trait for Test {
		type Origin = Origin;
		type Call = ();
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
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = Version;
		type ModuleToIndex = ();
	}

	impl From<Event> for u16 {
		fn from(e: Event) -> u16 {
			match e {
				Event::ExtrinsicSuccess(..) => 100,
				Event::ExtrinsicFailed(..) => 101,
				Event::CodeUpdated => 102,
			}
		}
	}

	type System = Module<Test>;

	const CALL: &<Test as Trait>::Call = &();

	fn new_test_ext() -> sp_io::TestExternalities {
		GenesisConfig::default().build_storage::<Test>().unwrap().into()
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
			System::deposit_event(42u16);
			System::note_applied_extrinsic(&Ok(()), 0, Default::default());
			System::note_applied_extrinsic(&Err(DispatchError::BadOrigin), 0, Default::default());
			System::note_finished_extrinsics();
			System::deposit_event(3u16);
			System::finalize();
			assert_eq!(
				System::events(),
				vec![
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
			<AccountNonce<Test>>::insert(1, 1);
			let info = DispatchInfo::default();
			let len = 0_usize;
			// stale
			assert!(CheckNonce::<Test>(0).validate(&1, CALL, info, len).is_err());
			assert!(CheckNonce::<Test>(0).pre_dispatch(&1, CALL, info, len).is_err());
			// correct
			assert!(CheckNonce::<Test>(1).validate(&1, CALL, info, len).is_ok());
			assert!(CheckNonce::<Test>(1).pre_dispatch(&1, CALL, info, len).is_ok());
			// future
			assert!(CheckNonce::<Test>(5).validate(&1, CALL, info, len).is_ok());
			assert!(CheckNonce::<Test>(5).pre_dispatch(&1, CALL, info, len).is_err());
		})
	}

	#[test]
	fn signed_ext_check_weight_works_normal_tx() {
		new_test_ext().execute_with(|| {
			let normal_limit = normal_weight_limit();
			let small = DispatchInfo { weight: 100, ..Default::default() };
			let medium = DispatchInfo {
				weight: normal_limit - 1,
				..Default::default()
			};
			let big = DispatchInfo {
				weight: normal_limit + 1,
				..Default::default()
			};
			let len = 0_usize;

			let reset_check_weight = |i, f, s| {
				AllExtrinsicsWeight::put(s);
				let r = CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, i, len);
				if f { assert!(r.is_err()) } else { assert!(r.is_ok()) }
			};

			reset_check_weight(small, false, 0);
			reset_check_weight(medium, false, 0);
			reset_check_weight(big, true, 1);
		})
	}

	#[test]
	fn signed_ext_check_weight_fee_works() {
		new_test_ext().execute_with(|| {
			let free = DispatchInfo { weight: 0, ..Default::default() };
			let len = 0_usize;

			assert_eq!(System::all_extrinsics_weight(), 0);
			let r = CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, free, len);
			assert!(r.is_ok());
			assert_eq!(System::all_extrinsics_weight(), 0);
		})
	}

	#[test]
	fn signed_ext_check_weight_max_works() {
		new_test_ext().execute_with(|| {
			let max = DispatchInfo { weight: Weight::max_value(), ..Default::default() };
			let len = 0_usize;
			let normal_limit = normal_weight_limit();

			assert_eq!(System::all_extrinsics_weight(), 0);
			let r = CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, max, len);
			assert!(r.is_ok());
			assert_eq!(System::all_extrinsics_weight(), normal_limit);
		})
	}

	#[test]
	fn signed_ext_check_weight_works_operational_tx() {
		new_test_ext().execute_with(|| {
			let normal = DispatchInfo { weight: 100, ..Default::default() };
			let op = DispatchInfo { weight: 100, class: DispatchClass::Operational, pays_fee: true };
			let len = 0_usize;
			let normal_limit = normal_weight_limit();

			// given almost full block
			AllExtrinsicsWeight::put(normal_limit);
			// will not fit.
			assert!(CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, normal, len).is_err());
			// will fit.
			assert!(CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, op, len).is_ok());

			// likewise for length limit.
			let len = 100_usize;
			AllExtrinsicsLen::put(normal_length_limit());
			assert!(CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, normal, len).is_err());
			assert!(CheckWeight::<Test>(PhantomData).pre_dispatch(&1, CALL, op, len).is_ok());
		})
	}

	#[test]
	fn signed_ext_check_weight_priority_works() {
		new_test_ext().execute_with(|| {
			let normal = DispatchInfo { weight: 100, class: DispatchClass::Normal, pays_fee: true };
			let op = DispatchInfo { weight: 100, class: DispatchClass::Operational, pays_fee: true };
			let len = 0_usize;

			let priority = CheckWeight::<Test>(PhantomData)
				.validate(&1, CALL, normal, len)
				.unwrap()
				.priority;
			assert_eq!(priority, 100);

			let priority = CheckWeight::<Test>(PhantomData)
				.validate(&1, CALL, op, len)
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

			reset_check_weight(normal, normal_limit - 1, false);
			reset_check_weight(normal, normal_limit, false);
			reset_check_weight(normal, normal_limit + 1, true);

			// Operational ones don't have this limit.
			let op = DispatchInfo { weight: 0, class: DispatchClass::Operational, pays_fee: true };
			reset_check_weight(op, normal_limit, false);
			reset_check_weight(op, normal_limit + 100, false);
			reset_check_weight(op, 1024, false);
			reset_check_weight(op, 1025, true);
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
			let normal = DispatchInfo { weight: 100, class: DispatchClass::Normal, pays_fee: true };
			let len = 0_usize;
			let ext = (
				CheckWeight::<Test>(PhantomData),
				CheckEra::<Test>::from(Era::mortal(16, 256)),
			);
			System::set_block_number(17);
			<BlockHash<Test>>::insert(16, H256::repeat_byte(1));

			assert_eq!(ext.validate(&1, CALL, normal, len).unwrap().longevity, 15);
		})
	}


	#[test]
	fn set_code_checks_works() {
		struct CallInWasm(Vec<u8>);

		impl sp_core::traits::CallInWasm for CallInWasm {
			fn call_in_wasm(
				&self,
				_: &[u8],
				_: &str,
				_: &[u8],
				_: &mut dyn sp_externalities::Externalities,
			) -> Result<Vec<u8>, String> {
				Ok(self.0.clone())
			}
		}

		let test_data = vec![
			("test", 1, 2, Ok(())),
			("test", 1, 1, Err(Error::<Test>::SpecOrImplVersionNeedToIncrease)),
			("test2", 1, 1, Err(Error::<Test>::InvalidSpecName)),
			("test", 2, 1, Ok(())),
			("test", 0, 1, Err(Error::<Test>::SpecVersionNotAllowedToDecrease)),
			("test", 1, 0, Err(Error::<Test>::ImplVersionNotAllowedToDecrease)),
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
			System::set_code(
				RawOrigin::Root.into(),
				substrate_test_runtime_client::runtime::WASM_BINARY.to_vec(),
			).unwrap();

			assert_eq!(
				System::events(),
				vec![EventRecord { phase: Phase::ApplyExtrinsic(0), event: 102u16, topics: vec![] }],
			);
		});
	}
}
