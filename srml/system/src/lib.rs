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
use primitives::traits::{self, CheckEqual, SimpleArithmetic, SimpleBitOps, One, Bounded, Lookup,
	Hash, Member, MaybeDisplay, EnsureOrigin, Digest as DigestT, CurrentHeight, BlockNumberToHash,
	MaybeSerializeDebugButNotDeserialize, MaybeSerializeDebug, StaticLookup
};
#[cfg(any(feature = "std", test))]
use primitives::traits::Zero;
use substrate_primitives::storage::well_known_keys;
use srml_support::{
	storage, decl_module, decl_event, decl_storage, StorageDoubleMap, StorageValue,
	StorageMap, Parameter, for_each_tuple, traits::Contains
};
use safe_mix::TripletMix;
use parity_codec::{Encode, Decode};

#[cfg(any(feature = "std", test))]
use runtime_io::{twox_128, TestExternalities, Blake2Hasher};

#[cfg(any(feature = "std", test))]
use substrate_primitives::ChangesTrieConfiguration;

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
pub fn extrinsics_root<H: Hash, E: parity_codec::Encode>(extrinsics: &[E]) -> H::Output {
	extrinsics_data_root::<H>(extrinsics.iter().map(parity_codec::Encode::encode).collect())
}

/// Compute the trie root of a list of extrinsics.
pub fn extrinsics_data_root<H: Hash>(xts: Vec<Vec<u8>>) -> H::Output {
	let xts = xts.iter().map(Vec::as_slice).collect::<Vec<_>>();
	H::enumerated_trie_root(&xts)
}

pub trait Trait: 'static + Eq + Clone {
	/// The aggregated `Origin` type used by dispatchable calls.
	type Origin: Into<Result<RawOrigin<Self::AccountId>, Self::Origin>> + From<RawOrigin<Self::AccountId>>;

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

	/// Collection of (light-client-relevant) logs for a block to be included verbatim in the block header.
	type Digest:
		Parameter + Member + MaybeSerializeDebugButNotDeserialize + Default + traits::Digest<Hash = Self::Hash>;

	/// The user account identifier type for the runtime.
	type AccountId: Parameter + Member + MaybeSerializeDebug + MaybeDisplay + Ord + Default;

	/// Converting trait to take a source type and convert to `AccountId`.
	///
	/// Used to define the type and conversion mechanism for referencing accounts in transactions. It's perfectly
	/// reasonable for this to be an identity conversion (with the source type being `AccountId`), but other modules
	/// (e.g. Indices module) may provide more functional/efficient alternatives.
	type Lookup: StaticLookup<Target = Self::AccountId>;

	/// The block header.
	type Header: Parameter + traits::Header<
		Number = Self::BlockNumber,
		Hash = Self::Hash,
		Digest = Self::Digest
	>;

	/// The aggregated event type of the runtime.
	type Event: Parameter + Member + From<Event>;

	/// A piece of information that can be part of the digest (as a digest item).
	type Log: From<Log<Self>> + Into<DigestItemOf<Self>>;
}

pub type DigestItemOf<T> = <<T as Trait>::Digest as traits::Digest>::Item;

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Deposits an event into this block's event record.
		pub fn deposit_event(event: T::Event) {
			Self::deposit_event_indexed(&[], event);
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

pub type Log<T> = RawLog<
	<T as Trait>::Hash,
>;

/// A log in this module.
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawLog<Hash> {
	/// Changes trie has been computed for this block. Contains the root of
	/// changes trie.
	ChangesTrieRoot(Hash),
}

impl<Hash: Member> RawLog<Hash> {
	/// Try to cast the log entry as ChangesTrieRoot log entry.
	pub fn as_changes_trie_root(&self) -> Option<&Hash> {
		match *self {
			RawLog::ChangesTrieRoot(ref item) => Some(item),
		}
	}
}

// Implementation for tests outside of this crate.
#[cfg(any(feature = "std", test))]
impl From<RawLog<substrate_primitives::H256>> for primitives::testing::DigestItem {
	fn from(log: RawLog<substrate_primitives::H256>) -> primitives::testing::DigestItem {
		match log {
			RawLog::ChangesTrieRoot(root) => primitives::generic::DigestItem::ChangesTrieRoot(root),
		}
	}
}

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
		/// Total length in bytes for all extrinsics put together, for the current block.
		AllExtrinsicsLen: Option<u32>;
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
		Digest get(digest): T::Digest;
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

		build(|storage: &mut primitives::StorageOverlay, _: &mut primitives::ChildrenStorageOverlay, config: &GenesisConfig<T>| {
			use parity_codec::Encode;

			storage.insert(well_known_keys::EXTRINSIC_INDEX.to_vec(), 0u32.encode());

			if let Some(ref changes_trie_config) = config.changes_trie_config {
				storage.insert(
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
	/// This will update storage entries that correpond to the specified topics.
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
			let old_event_count = <EventCount<T>>::get();
			let new_event_count = match old_event_count.checked_add(1) {
				// We've reached the maximum number of events at this block, just
				// don't do anything and leave the event_count unaltered.
				None => return,
				Some(nc) => nc,
			};
			<EventCount<T>>::put(new_event_count);
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
		<ExtrinsicCount<T>>::get().unwrap_or_default()
	}

	/// Gets a total length of all executed extrinsics.
	pub fn all_extrinsics_len() -> u32 {
		<AllExtrinsicsLen<T>>::get().unwrap_or_default()
	}

	/// Start the execution of a particular block.
	pub fn initialize(
		number: &T::BlockNumber,
		parent_hash: &T::Hash,
		txs_root: &T::Hash,
		digest: &T::Digest,
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
		<EventCount<T>>::kill();
		<EventTopics<T>>::remove_prefix(&());
	}

	/// Remove temporary "environment" entries in storage.
	pub fn finalize() -> T::Header {
		<ExtrinsicCount<T>>::kill();
		<AllExtrinsicsLen<T>>::kill();

		let number = <Number<T>>::take();
		let parent_hash = <ParentHash<T>>::take();
		let mut digest = <Digest<T>>::take();
		let extrinsics_root = <ExtrinsicsRoot<T>>::take();
		let storage_root = T::Hashing::storage_root();
		let storage_changes_root = T::Hashing::storage_changes_root(parent_hash);

		// we can't compute changes trie root earlier && put it to the Digest
		// because it will include all currently existing temporaries.
		if let Some(storage_changes_root) = storage_changes_root {
			let item = RawLog::ChangesTrieRoot(storage_changes_root);
			let item = <T as Trait>::Log::from(item).into();
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
	pub fn deposit_log(item: <T::Digest as traits::Digest>::Item) {
		let mut l = <Digest<T>>::get();
		traits::Digest::push(&mut l, item);
		<Digest<T>>::put(l);
	}

	/// Get the basic externalities for this module, useful for tests.
	#[cfg(any(feature = "std", test))]
	pub fn externalities() -> TestExternalities<Blake2Hasher> {
		TestExternalities::new(map![
			twox_128(&<BlockHash<T>>::key_for(T::BlockNumber::zero())).to_vec() => [69u8; 32].encode(),
			twox_128(<Number<T>>::key()).to_vec() => T::BlockNumber::one().encode(),
			twox_128(<ParentHash<T>>::key()).to_vec() => [69u8; 32].encode()
		])
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
		<ExtrinsicData<T>>::insert(Self::extrinsic_index().unwrap_or_default(), encoded_xt);
	}

	/// To be called immediately after an extrinsic has been applied.
	pub fn note_applied_extrinsic(r: &Result<(), &'static str>, encoded_len: u32) {
		Self::deposit_event(match r {
			Ok(_) => Event::ExtrinsicSuccess,
			Err(_) => Event::ExtrinsicFailed,
		}.into());

		let next_extrinsic_index = Self::extrinsic_index().unwrap_or_default() + 1u32;
		let total_length = encoded_len.saturating_add(Self::all_extrinsics_len());

		storage::unhashed::put(well_known_keys::EXTRINSIC_INDEX, &next_extrinsic_index);
		<AllExtrinsicsLen<T>>::put(&total_length);
	}

	/// To be called immediately after `note_applied_extrinsic` of the last extrinsic of the block
	/// has been called.
	pub fn note_finished_extrinsics() {
		let extrinsic_index: u32 = storage::unhashed::take(well_known_keys::EXTRINSIC_INDEX).unwrap_or_default();
		<ExtrinsicCount<T>>::put(extrinsic_index);
	}

	/// Remove all extrinsic data and save the extrinsics trie root.
	pub fn derive_extrinsics() {
		let extrinsics = (0..<ExtrinsicCount<T>>::get().unwrap_or_default()).map(<ExtrinsicData<T>>::take).collect();
		let xts_root = extrinsics_data_root::<T::Hashing>(extrinsics);
		<ExtrinsicsRoot<T>>::put(xts_root);
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

impl<T: Trait> CurrentHeight for ChainContext<T> {
	type BlockNumber = T::BlockNumber;
	fn current_height(&self) -> Self::BlockNumber {
		<Module<T>>::block_number()
	}
}

impl<T: Trait> BlockNumberToHash for ChainContext<T> {
	type BlockNumber = T::BlockNumber;
	type Hash = T::Hash;
	fn block_number_to_hash(&self, n: Self::BlockNumber) -> Option<Self::Hash> {
		Some(<Module<T>>::block_hash(n))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::with_externalities;
	use substrate_primitives::H256;
	use primitives::BuildStorage;
	use primitives::traits::{BlakeTwo256, IdentityLookup};
	use primitives::testing::{Digest, DigestItem, Header};
	use srml_support::impl_outer_origin;

	impl_outer_origin!{
		pub enum Origin for Test where system = super {}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = u16;
		type Log = DigestItem;
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

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		GenesisConfig::<Test>::default().build_storage().unwrap().0.into()
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
}
