// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
//! ## Usage
//!
//! ### Prerequisites
//!
//! Import the System module and derive your module's configuration trait from the system trait.
//!
//! ### Example - Get random seed and extrinsic count for the current block
//!
//! ```
//! use srml_support::{decl_module, dispatch::Result};
//! use srml_system::{self as system, ensure_signed};
//!
//! pub trait Trait: system::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		pub fn system_module_example(origin) -> Result {
//! 			let _sender = ensure_signed(origin)?;
//! 			let _random_seed = <system::Module<T>>::random_seed();
//! 			let _extrinsic_count = <system::Module<T>>::extrinsic_count();
//! 			Ok(())
//! 		}
//! 	}
//! }
//! # fn main() { }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::Serialize;
use rstd::prelude::*;
#[cfg(any(feature = "std", test))]
use rstd::map;
use rstd::marker::PhantomData;
use sr_version::RuntimeVersion;
use sr_primitives::generic::{self, Era};
use sr_primitives::Perbill;
use sr_primitives::weights::{
	Weight, DispatchInfo, DispatchClass, WeightMultiplier, SimpleDispatchInfo
};
use sr_primitives::transaction_validity::{
	ValidTransaction, TransactionPriority, TransactionLongevity
};
use sr_primitives::traits::{self, CheckEqual, SimpleArithmetic, Zero, SignedExtension, Convert,
	SimpleBitOps, Hash, Member, MaybeDisplay, EnsureOrigin, DispatchError, SaturatedConversion,
	MaybeSerializeDebugButNotDeserialize, MaybeSerializeDebug, StaticLookup, One, Bounded, Lookup,
};
use primitives::storage::well_known_keys;
use srml_support::{
	storage, decl_module, decl_event, decl_storage, StorageDoubleMap, StorageValue, StorageMap,
	Parameter, for_each_tuple, traits::{Contains, Get}
};
use safe_mix::TripletMix;
use codec::{Encode, Decode};

#[cfg(any(feature = "std", test))]
use runtime_io::{twox_128, TestExternalities, Blake2Hasher};

#[cfg(any(feature = "std", test))]
use primitives::ChangesTrieConfiguration;

/// Handler for when a new account has been created.
pub trait OnNewAccount<AccountId> {
	/// A new account `who` has been registered.
	fn on_new_account(who: &AccountId);
}

macro_rules! impl_on_new_account {
	() => (
		impl<AccountId> OnNewAccount<AccountId> for () {
			fn on_new_account(_: &AccountId) {}
		}
	);

	( $($t:ident)* ) => {
		impl<AccountId, $($t: OnNewAccount<AccountId>),*> OnNewAccount<AccountId> for ($($t,)*) {
			fn on_new_account(who: &AccountId) {
				$($t::on_new_account(who);)*
			}
		}
	}
}

for_each_tuple!(impl_on_new_account);

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
	let xts = xts.iter().map(Vec::as_slice).collect::<Vec<_>>();
	H::ordered_trie_root(&xts)
}

pub trait Trait: 'static + Eq + Clone {
	/// The aggregated `Origin` type used by dispatchable calls.
	type Origin: Into<Result<RawOrigin<Self::AccountId>, Self::Origin>> + From<RawOrigin<Self::AccountId>>;

	/// The aggregated `Call` type.
	type Call;

	/// Account index (aka nonce) type. This stores the number of previous transactions associated with a sender
	/// account.
	type Index:
		Parameter + Member + MaybeSerializeDebugButNotDeserialize + Default + MaybeDisplay + SimpleArithmetic + Copy;

	/// The block number type used by the runtime.
	type BlockNumber:
		Parameter + Member + MaybeSerializeDebug + MaybeDisplay + SimpleArithmetic + Default + Bounded + Copy
		+ rstd::hash::Hash;

	/// The output of the `Hashing` function.
	type Hash:
		Parameter + Member + MaybeSerializeDebug + MaybeDisplay + SimpleBitOps + Default + Copy + CheckEqual
		+ rstd::hash::Hash + AsRef<[u8]> + AsMut<[u8]>;

	/// The hashing system (algorithm) being used in the runtime (e.g. Blake2).
	type Hashing: Hash<Output = Self::Hash>;

	/// The user account identifier type for the runtime.
	type AccountId: Parameter + Member + MaybeSerializeDebug + MaybeDisplay + Ord + Default;

	/// Converting trait to take a source type and convert to `AccountId`.
	///
	/// Used to define the type and conversion mechanism for referencing accounts in transactions. It's perfectly
	/// reasonable for this to be an identity conversion (with the source type being `AccountId`), but other modules
	/// (e.g. Indices module) may provide more functional/efficient alternatives.
	type Lookup: StaticLookup<Target = Self::AccountId>;

	/// Handler for updating the weight multiplier at the end of each block.
	///
	/// It receives the current block's weight as input and returns the next weight multiplier for next
	/// block.
	///
	/// Note that passing `()` will keep the value constant.
	type WeightMultiplierUpdate: Convert<(Weight, WeightMultiplier), WeightMultiplier>;

	/// The block header.
	type Header: Parameter + traits::Header<
		Number = Self::BlockNumber,
		Hash = Self::Hash,
	>;

	/// The aggregated event type of the runtime.
	type Event: Parameter + Member + From<Event>;

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
}

pub type DigestOf<T> = generic::Digest<<T as Trait>::Hash>;
pub type DigestItemOf<T> = generic::DigestItem<<T as Trait>::Hash>;

pub type Key = Vec<u8>;
pub type KeyValue = (Vec<u8>, Vec<u8>);

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Deposits an event into this block's event record.
		pub fn deposit_event(event: T::Event) {
			Self::deposit_event_indexed(&[], event);
		}

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

		/// Set the new code.
		#[weight = SimpleDispatchInfo::FixedOperational(200_000)]
		pub fn set_code(origin, new: Vec<u8>) {
			ensure_root(origin)?;
			storage::unhashed::put_raw(well_known_keys::CODE, &new);
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
	}
}

/// A phase of a block's execution.
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Serialize, PartialEq, Eq, Clone, Debug))]
pub enum Phase {
	/// Applying an extrinsic.
	ApplyExtrinsic(u32),
	/// The end.
	Finalization,
}

/// Record of an event happening.
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Serialize, PartialEq, Eq, Clone, Debug))]
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
		ExtrinsicSuccess,
		/// An extrinsic failed.
		ExtrinsicFailed,
	}
);

/// Origin for the System module.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
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
		pub AccountNonce get(account_nonce): map T::AccountId => T::Index;
		/// Total extrinsics count for the current block.
		ExtrinsicCount: Option<u32>;
		/// Total weight for all extrinsics put together, for the current block.
		AllExtrinsicsWeight: Option<Weight>;
		/// Total length (in bytes) for all extrinsics put together, for the current block.
		AllExtrinsicsLen: Option<u32>;
		/// The next weight multiplier. This should be updated at the end of each block based on the
		/// saturation level (weight).
		pub NextWeightMultiplier get(next_weight_multiplier): WeightMultiplier = Default::default();
		/// Map of block numbers to block hashes.
		pub BlockHash get(block_hash) build(|_| vec![(T::BlockNumber::zero(), hash69())]): map T::BlockNumber => T::Hash;
		/// Extrinsics data for the current block (maps an extrinsic's index to its data).
		ExtrinsicData get(extrinsic_data): map u32 => Vec<u8>;
		/// Series of block headers from the last 81 blocks that acts as random seed material. This is arranged as a
		/// ring buffer with the `i8` prefix being the index into the `Vec` of the oldest hash.
		RandomMaterial get(random_material): (i8, Vec<T::Hash>);
		/// The current block number being processed. Set by `execute_block`.
		Number get(block_number) build(|_| 1.into()): T::BlockNumber;
		/// Hash of the previous block.
		ParentHash get(parent_hash) build(|_| hash69()): T::Hash;
		/// Extrinsics root of the current block, also part of the block header.
		ExtrinsicsRoot get(extrinsics_root): T::Hash;
		/// Digest of the current block, also part of the block header.
		Digest get(digest): DigestOf<T>;
		/// Events deposited for the current block.
		Events get(events): Vec<EventRecord<T::Event, T::Hash>>;
		/// The number of events in the `Events<T>` list.
		EventCount get(event_count): EventIndex;

		// TODO: https://github.com/paritytech/substrate/issues/2553
		// Possibly, we can improve it by using something like:
		// `Option<(BlockNumber, Vec<EventIndex>)>`, however in this case we won't be able to use
		// `EventTopics::append`.

		/// Mapping between a topic (represented by T::Hash) and a vector of indexes
		/// of events in the `<Events<T>>` list.
		///
		/// The first key serves no purpose. This field is declared as double_map just
		/// for convenience of using `remove_prefix`.
		///
		/// All topic vectors have deterministic storage locations depending on the topic. This
		/// allows light-clients to leverage the changes trie storage tracking mechanism and
		/// in case of changes fetch the list of events of interest.
		///
		/// The value has the type `(T::BlockNumber, EventIndex)` because if we used only just
		/// the `EventIndex` then in case if the topic has the same contents on the next block
		/// no notification will be triggered thus the event might be lost.
		EventTopics get(event_topics): double_map hasher(blake2_256) (), blake2_256(T::Hash)
			=> Vec<(T::BlockNumber, EventIndex)>;
	}
	add_extra_genesis {
		config(changes_trie_config): Option<ChangesTrieConfiguration>;
		#[serde(with = "primitives::bytes")]
		config(code): Vec<u8>;

		build(
			|storage: &mut (sr_primitives::StorageOverlay, sr_primitives::ChildrenStorageOverlay),
			config: &GenesisConfig|
		{
			use codec::Encode;

			storage.0.insert(well_known_keys::CODE.to_vec(), config.code.clone());
			storage.0.insert(well_known_keys::EXTRINSIC_INDEX.to_vec(), 0u32.encode());

			if let Some(ref changes_trie_config) = config.changes_trie_config {
				storage.0.insert(
					well_known_keys::CHANGES_TRIE_CONFIG.to_vec(),
					changes_trie_config.encode());
			}
		});
	}
}

pub struct EnsureRoot<AccountId>(::rstd::marker::PhantomData<AccountId>);
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

pub struct EnsureSigned<AccountId>(::rstd::marker::PhantomData<AccountId>);
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

pub struct EnsureSignedBy<Who, AccountId>(::rstd::marker::PhantomData<(Who, AccountId)>);
impl<
	O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
	Who: Contains<AccountId>,
	AccountId: PartialEq + Clone,
> EnsureOrigin<O> for EnsureSignedBy<Who, AccountId> {
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Signed(ref who) if Who::contains(who) => Ok(who.clone()),
			r => Err(O::from(r)),
		})
	}
}

pub struct EnsureNone<AccountId>(::rstd::marker::PhantomData<AccountId>);
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

pub struct EnsureNever<T>(::rstd::marker::PhantomData<T>);
impl<O, T> EnsureOrigin<O> for EnsureNever<T> {
	type Success = T;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		Err(o)
	}
}

/// Ensure that the origin `o` represents a signed extrinsic (i.e. transaction).
/// Returns `Ok` with the account that signed the extrinsic or an `Err` otherwise.
pub fn ensure_signed<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<AccountId, &'static str>
	where OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>
{
	match o.into() {
		Ok(RawOrigin::Signed(t)) => Ok(t),
		_ => Err("bad origin: expected to be a signed origin"),
	}
}

/// Ensure that the origin `o` represents the root. Returns `Ok` or an `Err` otherwise.
pub fn ensure_root<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), &'static str>
	where OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>
{
	match o.into() {
		Ok(RawOrigin::Root) => Ok(()),
		_ => Err("bad origin: expected to be a root origin"),
	}
}

/// Ensure that the origin `o` represents an unsigned extrinsic. Returns `Ok` or an `Err` otherwise.
pub fn ensure_none<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), &'static str>
	where OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>
{
	match o.into() {
		Ok(RawOrigin::None) => Ok(()),
		_ => Err("bad origin: expected to be no origin"),
	}
}

impl<T: Trait> Module<T> {
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
		if <Events<T>>::append(&[event]).is_err() {
			// The most sensible thing to do here is to just ignore this event and wait until the
			// new block.
			return;
		}

		let block_no = Self::block_number();
		for topic in topics {
			// The same applies here.
			if <EventTopics<T>>::append(&(), topic, &[(block_no, event_idx)]).is_err() {
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

	/// Update the next weight multiplier.
	///
	/// This should be called at then end of each block, before `all_extrinsics_weight` is cleared.
	pub fn update_weight_multiplier() {
		// update the multiplier based on block weight.
		let current_weight = Self::all_extrinsics_weight();
		NextWeightMultiplier::mutate(|fm| {
			*fm = T::WeightMultiplierUpdate::convert((current_weight, *fm))
		});
	}

	/// Start the execution of a particular block.
	pub fn initialize(
		number: &T::BlockNumber,
		parent_hash: &T::Hash,
		txs_root: &T::Hash,
		digest: &DigestOf<T>,
	) {
		// populate environment
		storage::unhashed::put(well_known_keys::EXTRINSIC_INDEX, &0u32);
		<Number<T>>::put(number);
		<Digest<T>>::put(digest);
		<ParentHash<T>>::put(parent_hash);
		<BlockHash<T>>::insert(*number - One::one(), parent_hash);
		<ExtrinsicsRoot<T>>::put(txs_root);
		<RandomMaterial<T>>::mutate(|&mut(ref mut index, ref mut values)| if values.len() < 81 {
			values.push(parent_hash.clone())
		} else {
			values[*index as usize] = parent_hash.clone();
			*index = (*index + 1) % 81;
		});
		<Events<T>>::kill();
		EventCount::kill();
		<EventTopics<T>>::remove_prefix(&());
	}

	/// Remove temporary "environment" entries in storage.
	pub fn finalize() -> T::Header {
		ExtrinsicCount::kill();
		Self::update_weight_multiplier();
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

		let storage_root = T::Hashing::storage_root();
		let storage_changes_root = T::Hashing::storage_changes_root(parent_hash);

		// we can't compute changes trie root earlier && put it to the Digest
		// because it will include all currently existing temporaries.
		if let Some(storage_changes_root) = storage_changes_root {
			let item = generic::DigestItem::ChangesTrieRoot(storage_changes_root);
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
	pub fn externalities() -> TestExternalities<Blake2Hasher> {
		TestExternalities::new((map![
			twox_128(&<BlockHash<T>>::key_for(T::BlockNumber::zero())).to_vec() => [69u8; 32].encode(),
			twox_128(<Number<T>>::key()).to_vec() => T::BlockNumber::one().encode(),
			twox_128(<ParentHash<T>>::key()).to_vec() => [69u8; 32].encode()
		], map![]))
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

	/// Return the chain's current runtime version.
	pub fn runtime_version() -> RuntimeVersion { T::Version::get() }

	/// Get the basic random seed.
	///
	/// In general you won't want to use this, but rather `Self::random` which
	/// allows you to give a subject for the random result and whose value will
	/// be independently low-influence random from any other such seeds.
	pub fn random_seed() -> T::Hash {
		Self::random(&[][..])
	}

	/// Get a low-influence "random" value.
	///
	/// Being a deterministic block chain, real randomness is difficult to come
	/// by. This gives you something that approximates it. `subject` is a
	/// context identifier and allows you to get a different result to other
	/// callers of this function; use it like `random(&b"my context"[..])`.
	///
	/// This is initially implemented through a low-influence "triplet mix"
	/// convolution of previous block hash values. In the future it will be
	/// generated from a secure verifiable random function (VRF).
	///
	/// ### Security Notes
	///
	/// This randomness uses a low-influence function, drawing upon the block
	/// hashes from the previous 81 blocks. Its result for any given subject
	/// will be known in advance by the block producer of this block (and,
	/// indeed, anyone who knows the block's `parent_hash`). However, it is
	/// mostly impossible for the producer of this block *alone* to influence
	/// the value of this hash. A sizable minority of dishonest and coordinating
	/// block producers would be required in order to affect this value. If that
	/// is an insufficient security guarantee then two things can be used to
	/// improve this randomness:
	///
	/// - Name, in advance, the block number whose random value will be used;
	///   ensure your module retains a buffer of previous random values for its
	///   subject and then index into these in order to obviate the ability of
	///   your user to look up the parent hash and choose when to transact based
	///   upon it.
	/// - Require your user to first commit to an additional value by first
	///   posting its hash. Require them to reveal the value to determine the
	///   final result, hashing it with the output of this random function. This
	///   reduces the ability of a cabal of block producers from conspiring
	///   against individuals.
	///
	/// WARNING: Hashing the result of this function will remove any
	/// low-influnce properties it has and mean that all bits of the resulting
	/// value are entirely manipulatable by the author of the parent block, who
	/// can determine the value of `parent_hash`.
	pub fn random(subject: &[u8]) -> T::Hash {
		let (index, hash_series) = <RandomMaterial<T>>::get();
		if hash_series.len() > 0 {
			// Always the case after block 1 is initialised.
			hash_series.iter()
				.cycle()
				.skip(index as usize)
				.take(81)
				.enumerate()
				.map(|(i, h)| (i as i8, subject, h).using_encoded(T::Hashing::hash))
				.triplet_mix()
		} else {
			T::Hash::default()
		}
	}

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
	pub fn note_applied_extrinsic(r: &Result<(), &'static str>, _encoded_len: u32) {
		Self::deposit_event(match r {
			Ok(_) => Event::ExtrinsicSuccess,
			Err(_) => Event::ExtrinsicFailed,
		}.into());

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
			// TODO: this must be some sort of a constant.
			DispatchClass::Normal => T::AvailableBlockRatio::get(),
		}
	}

	/// Checks if the current extrinsic can fit into the block with respect to block weight limits.
	///
	/// Upon successes, it returns the new block weight as a `Result`.
	fn check_weight(info: DispatchInfo) -> Result<Weight, DispatchError> {
		let current_weight = Module::<T>::all_extrinsics_weight();
		let maximum_weight = T::MaximumBlockWeight::get();
		let limit = Self::get_dispatch_limit_ratio(info.class) * maximum_weight;
		let added_weight = info.weight.min(limit);
		let next_weight = current_weight.saturating_add(added_weight);
		if next_weight > limit {
			return Err(DispatchError::Exhausted)
		}
		Ok(next_weight)
	}

	/// Checks if the current extrinsic can fit into the block with respect to block length limits.
	///
	/// Upon successes, it returns the new block length as a `Result`.
	fn check_block_length(info: DispatchInfo, len: usize) -> Result<u32, DispatchError> {
		let current_len = Module::<T>::all_extrinsics_len();
		let maximum_len = T::MaximumBlockLength::get();
		let limit = Self::get_dispatch_limit_ratio(info.class) * maximum_len;
		let added_len = len as u32;
		let next_len = current_len.saturating_add(added_len);
		if next_len > limit {
			return Err(DispatchError::Exhausted)
		}
		Ok(next_len)
	}

	/// get the priority of an extrinsic denoted by `info`.
	fn get_priority(info: DispatchInfo) -> TransactionPriority {
		match info.class {
			DispatchClass::Normal => info.weight.into(),
			DispatchClass::Operational => Bounded::max_value()
		}
	}

	/// Utility constructor for tests and client code.
	#[cfg(feature = "std")]
	pub fn new() -> Self {
		Self(PhantomData)
	}
}

impl<T: Trait + Send + Sync> SignedExtension for CheckWeight<T> {
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type Pre = ();

	fn additional_signed(&self) -> rstd::result::Result<(), &'static str> { Ok(()) }

	fn pre_dispatch(
		self,
		_who: &Self::AccountId,
		_call: &Self::Call,
		info: DispatchInfo,
		len: usize,
	) -> Result<(), DispatchError> {
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
		info: DispatchInfo,
		len: usize,
	) -> Result<ValidTransaction, DispatchError> {
		// There is no point in writing to storage here since changes are discarded. This basically
		// discards any transaction which is bigger than the length or weight limit **alone**,which
		// is a guarantee that it will fail in the pre-dispatch phase.
		let _ = Self::check_block_length(info, len)?;
		let _ = Self::check_weight(info)?;
		Ok(ValidTransaction { priority: Self::get_priority(info), ..Default::default() })
	}
}

#[cfg(feature = "std")]
impl<T: Trait + Send + Sync> rstd::fmt::Debug for CheckWeight<T> {
	fn fmt(&self, f: &mut rstd::fmt::Formatter) -> rstd::fmt::Result {
		write!(f, "CheckWeight<T>")
	}
}

/// Nonce check and increment to give replay protection for transactions.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckNonce<T: Trait>(#[codec(compact)] T::Index);

#[cfg(feature = "std")]
impl<T: Trait> CheckNonce<T> {
	/// utility constructor. Used only in client/factory code.
	pub fn from(nonce: T::Index) -> Self {
		Self(nonce)
	}
}

#[cfg(feature = "std")]
impl<T: Trait> rstd::fmt::Debug for CheckNonce<T> {
	fn fmt(&self, f: &mut rstd::fmt::Formatter) -> rstd::fmt::Result {
		self.0.fmt(f)
	}
}

impl<T: Trait> SignedExtension for CheckNonce<T> {
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type Pre = ();

	fn additional_signed(&self) -> rstd::result::Result<(), &'static str> { Ok(()) }

	fn pre_dispatch(
		self,
		who: &Self::AccountId,
		_call: &Self::Call,
		_info: DispatchInfo,
		_len: usize,
	) -> Result<(), DispatchError> {
		let expected = <AccountNonce<T>>::get(who);
		if self.0 != expected {
			return Err(
				if self.0 < expected { DispatchError::Stale } else { DispatchError::Future }
			)
		}
		<AccountNonce<T>>::insert(who, expected + T::Index::one());
		Ok(())
	}

	fn validate(
		&self,
		who: &Self::AccountId,
		_call: &Self::Call,
		info: DispatchInfo,
		_len: usize,
	) -> Result<ValidTransaction, DispatchError> {
		// check index
		let expected = <AccountNonce<T>>::get(who);
		if self.0 < expected {
			return Err(DispatchError::Stale)
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

/// Nonce check and increment to give replay protection for transactions.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckEra<T: Trait + Send + Sync>((Era, rstd::marker::PhantomData<T>));

#[cfg(feature = "std")]
impl<T: Trait + Send + Sync> CheckEra<T> {
	/// utility constructor. Used only in client/factory code.
	pub fn from(era: Era) -> Self {
		Self((era, rstd::marker::PhantomData))
	}
}

#[cfg(feature = "std")]
impl<T: Trait + Send + Sync> rstd::fmt::Debug for CheckEra<T> {
	fn fmt(&self, f: &mut rstd::fmt::Formatter) -> rstd::fmt::Result {
		self.0.fmt(f)
	}
}

impl<T: Trait + Send + Sync> SignedExtension for CheckEra<T> {
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = T::Hash;
	type Pre = ();

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, &'static str> {
		let current_u64 = <Module<T>>::block_number().saturated_into::<u64>();
		let n = (self.0).0.birth(current_u64).saturated_into::<T::BlockNumber>();
		if !<BlockHash<T>>::exists(n) { Err("transaction birth block ancient")? }
		Ok(<Module<T>>::block_hash(n))
	}
}

/// Nonce check and increment to give replay protection for transactions.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckGenesis<T: Trait + Send + Sync>(rstd::marker::PhantomData<T>);

#[cfg(feature = "std")]
impl<T: Trait + Send + Sync> rstd::fmt::Debug for CheckGenesis<T> {
	fn fmt(&self, _f: &mut rstd::fmt::Formatter) -> rstd::fmt::Result {
		Ok(())
	}
}

#[cfg(feature = "std")]
impl<T: Trait + Send + Sync> CheckGenesis<T> {
	pub fn new() -> Self {
		Self(std::marker::PhantomData)
	}
}

impl<T: Trait + Send + Sync> SignedExtension for CheckGenesis<T> {
	type AccountId = T::AccountId;
	type Call = <T as Trait>::Call;
	type AdditionalSigned = T::Hash;
	type Pre = ();

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, &'static str> {
		Ok(<Module<T>>::block_hash(T::BlockNumber::zero()))
	}
}

/// Ensure the runtime version registered in the transaction is the same as at present.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct CheckVersion<T: Trait + Send + Sync>(rstd::marker::PhantomData<T>);

#[cfg(feature = "std")]
impl<T: Trait + Send + Sync> rstd::fmt::Debug for CheckVersion<T> {
	fn fmt(&self, _f: &mut rstd::fmt::Formatter) -> rstd::fmt::Result {
		Ok(())
	}
}

#[cfg(feature = "std")]
impl<T: Trait + Send + Sync> CheckVersion<T> {
	pub fn new() -> Self {
		Self(std::marker::PhantomData)
	}
}

impl<T: Trait + Send + Sync> SignedExtension for CheckVersion<T> {
	type AccountId = T::AccountId;
	type Call = <T as Trait>::Call;
	type AdditionalSigned = u32;
	type Pre = ();

	fn additional_signed(&self) -> Result<Self::AdditionalSigned, &'static str> {
		Ok(<Module<T>>::runtime_version().spec_version)
	}
}

pub struct ChainContext<T>(::rstd::marker::PhantomData<T>);
impl<T> Default for ChainContext<T> {
	fn default() -> Self {
		ChainContext(::rstd::marker::PhantomData)
	}
}

impl<T: Trait> Lookup for ChainContext<T> {
	type Source = <T::Lookup as StaticLookup>::Source;
	type Target = <T::Lookup as StaticLookup>::Target;
	fn lookup(&self, s: Self::Source) -> rstd::result::Result<Self::Target, &'static str> {
		<T::Lookup as StaticLookup>::lookup(s)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::with_externalities;
	use primitives::H256;
	use sr_primitives::{traits::{BlakeTwo256, IdentityLookup}, testing::Header};
	use srml_support::{impl_outer_origin, parameter_types};

	impl_outer_origin!{
		pub enum Origin for Test where system = super {}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;

	parameter_types! {
		pub const BlockHashCount: u64 = 10;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);
		pub const MaximumBlockLength: u32 = 1024;
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
		type WeightMultiplierUpdate = ();
		type Event = u16;
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = ();
	}

	impl From<Event> for u16 {
		fn from(e: Event) -> u16 {
			match e {
				Event::ExtrinsicSuccess => 100,
				Event::ExtrinsicFailed => 101,
			}
		}
	}

	type System = Module<Test>;

	const CALL: &<Test as Trait>::Call = &();

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
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
		with_externalities(&mut new_test_ext(), || {
			System::initialize(&1, &[0u8; 32].into(), &[0u8; 32].into(), &Default::default());
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

			System::initialize(&2, &[0u8; 32].into(), &[0u8; 32].into(), &Default::default());
			System::deposit_event(42u16);
			System::note_applied_extrinsic(&Ok(()), 0);
			System::note_applied_extrinsic(&Err(""), 0);
			System::note_finished_extrinsics();
			System::deposit_event(3u16);
			System::finalize();
			assert_eq!(System::events(), vec![
				EventRecord { phase: Phase::ApplyExtrinsic(0), event: 42u16, topics: vec![] },
				EventRecord { phase: Phase::ApplyExtrinsic(0), event: 100u16, topics: vec![] },
				EventRecord { phase: Phase::ApplyExtrinsic(1), event: 101u16, topics: vec![] },
				EventRecord { phase: Phase::Finalization, event: 3u16, topics: vec![] }
			]);
		});
	}

	#[test]
	fn deposit_event_topics() {
		with_externalities(&mut new_test_ext(), || {
			const BLOCK_NUMBER: u64 = 1;

			System::initialize(&BLOCK_NUMBER, &[0u8; 32].into(), &[0u8; 32].into(), &Default::default());
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
				System::event_topics(&(), &topics[0]),
				vec![(BLOCK_NUMBER, 0), (BLOCK_NUMBER, 1)],
			);
			assert_eq!(
				System::event_topics(&(), &topics[1]),
				vec![(BLOCK_NUMBER, 0), (BLOCK_NUMBER, 2)],
			);
			assert_eq!(
				System::event_topics(&(), &topics[2]),
				vec![(BLOCK_NUMBER, 0)],
			);
		});
	}

	#[test]
	fn prunes_block_hash_mappings() {
		with_externalities(&mut new_test_ext(), || {
			// simulate import of 15 blocks
			for n in 1..=15 {
				System::initialize(
					&n,
					&[n as u8 - 1; 32].into(),
					&[0u8; 32].into(),
					&Default::default(),
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
		with_externalities(&mut new_test_ext(), || {
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
		with_externalities(&mut new_test_ext(), || {
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
		with_externalities(&mut new_test_ext(), || {
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
		with_externalities(&mut new_test_ext(), || {
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
		with_externalities(&mut new_test_ext(), || {
			let normal = DispatchInfo { weight: 100, ..Default::default() };
			let op = DispatchInfo { weight: 100, class: DispatchClass::Operational };
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
		with_externalities(&mut new_test_ext(), || {
			let normal = DispatchInfo { weight: 100, class: DispatchClass::Normal };
			let op = DispatchInfo { weight: 100, class: DispatchClass::Operational };
			let len = 0_usize;

			assert_eq!(
				CheckWeight::<Test>(PhantomData).validate(&1, CALL, normal, len).unwrap().priority,
				100,
			);
			assert_eq!(
				CheckWeight::<Test>(PhantomData).validate(&1, CALL, op, len).unwrap().priority,
				Bounded::max_value(),
			);
		})
	}

	#[test]
	fn signed_ext_check_weight_block_size_works() {
		with_externalities(&mut new_test_ext(), || {
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
			let op = DispatchInfo { weight: 0, class: DispatchClass::Operational };
			reset_check_weight(op, normal_limit, false);
			reset_check_weight(op, normal_limit + 100, false);
			reset_check_weight(op, 1024, false);
			reset_check_weight(op, 1025, true);
		})
	}

	#[test]
	fn signed_ext_check_era_should_work() {
		with_externalities(&mut new_test_ext(), || {
			// future
			assert_eq!(
				CheckEra::<Test>::from(Era::mortal(4, 2)).additional_signed().err().unwrap(),
				"transaction birth block ancient"
			);

			// correct
			System::set_block_number(13);
			<BlockHash<Test>>::insert(12, H256::repeat_byte(1));
			assert!(CheckEra::<Test>::from(Era::mortal(4, 12)).additional_signed().is_ok());
		})
	}
}
