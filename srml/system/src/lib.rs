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

//! # System module
//! 
//! The system module provides low-level access to core types and cross-cutting utilities.
//! It acts as the base layer for other SRML modules to interact with the Substrate framework components.
//! To use it in your module, you should ensure your module's trait implies the system [`Trait`].
//! 
//! ## Overview
//! 
//! The system module defines the core data types used in a Substrate runtime.
//! It also provides several utility functions (see [`Module`]) for other runtime modules.
//! 
//! In addition, it manages the storage items for extrinsics data, indexes, event record and digest items, 
//! among other things that support the execution of the current block.
//! 
//! It also handles low level tasks like depositing logs, basic set up and take down of
//! temporary storage entries and access to previous block hashes.
//! 
//! ## Interface
//! 
//! ### Dispatchable functions
//! 
//! The system module does not implement any dispatchable functions.
//! 
//! ### Public functions
//! 
//! All public functions are available as part of the [`Module`] type.
//! 
//! ## Usage
//! 
//! ### Prerequisites
//! 
//! Import the system module and derive your module's configuration trait from the system trait.
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
use serde_derive::Serialize;
use rstd::prelude::*;
#[cfg(any(feature = "std", test))]
use rstd::map;
use primitives::traits::{self, CheckEqual, SimpleArithmetic, SimpleBitOps, Zero, One, Bounded, Lookup,
	Hash, Member, MaybeDisplay, EnsureOrigin, Digest as DigestT, As, CurrentHeight, BlockNumberToHash,
	MaybeSerializeDebugButNotDeserialize, MaybeSerializeDebug, StaticLookup};
use substrate_primitives::storage::well_known_keys;
use srml_support::{storage, StorageValue, StorageMap, Parameter, decl_module, decl_event, decl_storage};
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

impl<AccountId> OnNewAccount<AccountId> for () {
	fn on_new_account(_who: &AccountId) {}
}

/// Determinator to say whether a given account is unused.
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
	type Origin: Into<Option<RawOrigin<Self::AccountId>>> + From<RawOrigin<Self::AccountId>>;

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

	/// A piece of information which can be part of the digest (as a digest item).
	type Log: From<Log<Self>> + Into<DigestItemOf<Self>>;
}

pub type DigestItemOf<T> = <<T as Trait>::Digest as traits::Digest>::Item;

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Deposits an event onto this block's event record.
		pub fn deposit_event(event: T::Event) {
			let extrinsic_index = Self::extrinsic_index();
			let phase = extrinsic_index.map_or(Phase::Finalization, |c| Phase::ApplyExtrinsic(c));
			let mut events = Self::events();
			events.push(EventRecord { phase, event });
			<Events<T>>::put(events);
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
pub struct EventRecord<E: Parameter + Member> {
	/// The phase of the block it happened in.
	pub phase: Phase,
	/// The event itself.
	pub event: E,
}

decl_event!(
	/// Event for the system module.
	pub enum Event {
		/// An extrinsic completed successfully.
		ExtrinsicSuccess,
		/// An extrinsic failed.
		ExtrinsicFailed,
	}
);

/// Origin for the system module.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum RawOrigin<AccountId> {
	/// The system itself ordained this dispatch to happen: this is the highest privilege level.
	Root,
	/// It is signed by some public key and we provide the AccountId.
	Signed(AccountId),
	/// It is signed by nobody but included and agreed upon by the validators anyway: it's "inherently" true.
	Inherent,
}

impl<AccountId> From<Option<AccountId>> for RawOrigin<AccountId> {
	fn from(s: Option<AccountId>) -> RawOrigin<AccountId> {
		match s {
			Some(who) => RawOrigin::Signed(who),
			None => RawOrigin::Inherent,
		}
	}
}

/// Exposed trait-generic origin type.
pub type Origin<T> = RawOrigin<<T as Trait>::AccountId>;

pub type Log<T> = RawLog<
	<T as Trait>::Hash,
>;

/// A logs in this module.
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
		/// Extrinsics data for the current block (maps extrinsic's index to its data).
		ExtrinsicData get(extrinsic_data): map u32 => Vec<u8>;
		/// Random seed of the current block.
		RandomSeed get(random_seed) build(|_| T::Hash::default()): T::Hash;
		/// The current block number being processed. Set by `execute_block`.
		Number get(block_number) build(|_| T::BlockNumber::sa(1u64)): T::BlockNumber;
		/// Hash of the previous block.
		ParentHash get(parent_hash) build(|_| hash69()): T::Hash;
		/// Extrinsics root of the current block, also part of the block header.
		ExtrinsicsRoot get(extrinsics_root): T::Hash;
		/// Digest of the current block, also part of the block header.
		Digest get(digest): T::Digest;
		/// Events deposited for the current block.
		Events get(events): Vec<EventRecord<T::Event>>;
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
impl<O: Into<Option<RawOrigin<AccountId>>>, AccountId> EnsureOrigin<O> for EnsureRoot<AccountId> {
	type Success = ();
	fn ensure_origin(o: O) -> Result<Self::Success, &'static str> {
		ensure_root(o)
	}
}

/// Ensure that the origin `o` represents a signed extrinsic (i.e. transaction).
/// Returns `Ok` with the account that signed the extrinsic or an `Err` otherwise.
pub fn ensure_signed<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<AccountId, &'static str>
	where OuterOrigin: Into<Option<RawOrigin<AccountId>>>
{
	match o.into() {
		Some(RawOrigin::Signed(t)) => Ok(t),
		_ => Err("bad origin: expected to be a signed origin"),
	}
}

/// Ensure that the origin `o` represents the root. Returns `Ok` or an `Err` otherwise.
pub fn ensure_root<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), &'static str>
	where OuterOrigin: Into<Option<RawOrigin<AccountId>>>
{
	match o.into() {
		Some(RawOrigin::Root) => Ok(()),
		_ => Err("bad origin: expected to be a root origin"),
	}
}

/// Ensure that the origin `o` represents an unsigned extrinsic. Returns `Ok` or an `Err` otherwise.
pub fn ensure_inherent<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), &'static str>
	where OuterOrigin: Into<Option<RawOrigin<AccountId>>>
{
	match o.into() {
		Some(RawOrigin::Inherent) => Ok(()),
		_ => Err("bad origin: expected to be an inherent origin"),
	}
}

impl<T: Trait> Module<T> {
	/// Gets the index of extrinsic that is currenty executing.
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
	pub fn initialize(number: &T::BlockNumber, parent_hash: &T::Hash, txs_root: &T::Hash) {
		// populate environment.
		storage::unhashed::put(well_known_keys::EXTRINSIC_INDEX, &0u32);
		<Number<T>>::put(number);
		<ParentHash<T>>::put(parent_hash);
		<BlockHash<T>>::insert(*number - One::one(), parent_hash);
		<ExtrinsicsRoot<T>>::put(txs_root);
		<RandomSeed<T>>::put(Self::calculate_random());
		<Events<T>>::kill();
	}

	/// Remove temporary "environment" entries in storage.
	pub fn finalize() -> T::Header {
		<RandomSeed<T>>::kill();
		<ExtrinsicCount<T>>::kill();
		<AllExtrinsicsLen<T>>::kill();

		let number = <Number<T>>::take();
		let parent_hash = <ParentHash<T>>::take();
		let mut digest = <Digest<T>>::take();
		let extrinsics_root = <ExtrinsicsRoot<T>>::take();
		let storage_root = T::Hashing::storage_root();
		let storage_changes_root = T::Hashing::storage_changes_root(parent_hash, number.as_() - 1);

		// we can't compute changes trie root earlier && put it to the Digest
		// because it will include all currently existing temporaries
		if let Some(storage_changes_root) = storage_changes_root {
			let item = RawLog::ChangesTrieRoot(storage_changes_root);
			let item = <T as Trait>::Log::from(item).into();
			digest.push(item);
		}

		// <Events<T>> stays to be inspected by the client.

		<T::Header as traits::Header>::new(number, extrinsics_root, storage_root, parent_hash, digest)
	}

	/// Deposits a log and ensures it matches the blocks log data.
	pub fn deposit_log(item: <T::Digest as traits::Digest>::Item) {
		let mut l = <Digest<T>>::get();
		traits::Digest::push(&mut l, item);
		<Digest<T>>::put(l);
	}

	/// Calculate the current block's random seed.
	fn calculate_random() -> T::Hash {
		assert!(Self::block_number() > Zero::zero(), "Block number may never be zero");
		(0..81)
			.scan(
				Self::block_number() - One::one(),
				|c, _| { if *c > Zero::zero() { *c -= One::one() }; Some(*c)
			})
			.map(Self::block_hash)
			.triplet_mix()
	}

	/// Get the basic externalities for this module, useful for tests.
	#[cfg(any(feature = "std", test))]
	pub fn externalities() -> TestExternalities<Blake2Hasher> {
		TestExternalities::new(map![
			twox_128(&<BlockHash<T>>::key_for(T::BlockNumber::zero())).to_vec() => [69u8; 32].encode(),
			twox_128(<Number<T>>::key()).to_vec() => T::BlockNumber::one().encode(),
			twox_128(<ParentHash<T>>::key()).to_vec() => [69u8; 32].encode(),
			twox_128(<RandomSeed<T>>::key()).to_vec() => T::Hash::default().encode()
		])
	}

	/// Set the block number to something in particular. Can be used as an alternative to
	/// `initialize` for tests that don't need to bother with the other environment entries.
	#[cfg(any(feature = "std", test))]
	pub fn set_block_number(n: T::BlockNumber) {
		<Number<T>>::put(n);
	}

	/// Sets the index of extrinsic that is currenty executing.
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

	/// Set the random seed to something in particular. Can be used as an alternative to
	/// `initialize` for tests that don't need to bother with the other environment entries.
	#[cfg(any(feature = "std", test))]
	pub fn set_random_seed(seed: T::Hash) {
		<RandomSeed<T>>::put(seed);
	}

	/// Increment a particular account's nonce by 1.
	pub fn inc_account_nonce(who: &T::AccountId) {
		<AccountNonce<T>>::insert(who, Self::account_nonce(who) + T::Index::one());
	}

	/// Note what the extrinsic data of the current extrinsic index is. If this is called, then
	/// ensure `derive_extrinsics` is also called before block-building is completed.
	///
	/// NOTE this function is called only when the block is being constructed locally.
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

	/// Remove all extrinsics data and save the extrinsics trie root.
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
	fn deposit_event_should_work() {
		with_externalities(&mut new_test_ext(), || {
			System::initialize(&1, &[0u8; 32].into(), &[0u8; 32].into());
			System::note_finished_extrinsics();
			System::deposit_event(1u16);
			System::finalize();
			assert_eq!(System::events(), vec![EventRecord { phase: Phase::Finalization, event: 1u16 }]);

			System::initialize(&2, &[0u8; 32].into(), &[0u8; 32].into());
			System::deposit_event(42u16);
			System::note_applied_extrinsic(&Ok(()), 0);
			System::note_applied_extrinsic(&Err(""), 0);
			System::note_finished_extrinsics();
			System::deposit_event(3u16);
			System::finalize();
			assert_eq!(System::events(), vec![
				EventRecord { phase: Phase::ApplyExtrinsic(0), event: 42u16 },
				EventRecord { phase: Phase::ApplyExtrinsic(0), event: 100u16 },
				EventRecord { phase: Phase::ApplyExtrinsic(1), event: 101u16 },
				EventRecord { phase: Phase::Finalization, event: 3u16 }
			]);
		});
	}
}
