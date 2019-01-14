// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! System manager: Handles lowest level stuff like depositing logs, basic set up and take down of
//! temporary storage entries, access to old block hashes.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate substrate_primitives;

#[cfg_attr(any(feature = "std", test), macro_use)]
extern crate sr_std as rstd;

#[macro_use]
extern crate srml_support as runtime_support;

#[macro_use]
extern crate parity_codec_derive;

extern crate parity_codec as codec;
extern crate sr_io as runtime_io;
extern crate sr_primitives as primitives;
extern crate safe_mix;

use rstd::prelude::*;
use primitives::traits::{self, CheckEqual, SimpleArithmetic, SimpleBitOps, Zero, One, Bounded, Lookup,
	Hash, Member, MaybeDisplay, EnsureOrigin, Digest as DigestT, As, CurrentHeight, BlockNumberToHash,
	MaybeSerializeDebugButNotDeserialize, MaybeSerializeDebug};
use substrate_primitives::storage::well_known_keys;
use runtime_support::{storage, StorageValue, StorageMap, Parameter};
use safe_mix::TripletMix;

#[cfg(any(feature = "std", test))]
use codec::Encode;

#[cfg(any(feature = "std", test))]
use runtime_io::{twox_128, TestExternalities, Blake2Hasher};

#[cfg(any(feature = "std", test))]
use substrate_primitives::ChangesTrieConfiguration;

/// Compute the extrinsics root of a list of extrinsics.
pub fn extrinsics_root<H: Hash, E: codec::Encode>(extrinsics: &[E]) -> H::Output {
	extrinsics_data_root::<H>(extrinsics.iter().map(codec::Encode::encode).collect())
}

/// Compute the extrinsics root of a list of extrinsics.
pub fn extrinsics_data_root<H: Hash>(xts: Vec<Vec<u8>>) -> H::Output {
	let xts = xts.iter().map(Vec::as_slice).collect::<Vec<_>>();
	H::enumerated_trie_root(&xts)
}

pub trait Trait: 'static + Eq + Clone {
	type Origin: Into<Option<RawOrigin<Self::AccountId>>> + From<RawOrigin<Self::AccountId>>;
	type Index: Parameter + Member + MaybeSerializeDebugButNotDeserialize + Default + MaybeDisplay + SimpleArithmetic + Copy;
	type BlockNumber: Parameter + Member + MaybeSerializeDebug + MaybeDisplay + SimpleArithmetic + Default + Bounded + Copy + rstd::hash::Hash;
	type Hash: Parameter + Member + MaybeSerializeDebug + MaybeDisplay + SimpleBitOps + Default + Copy + CheckEqual + rstd::hash::Hash + AsRef<[u8]> + AsMut<[u8]>;
	type Hashing: Hash<Output = Self::Hash>;
	type Digest: Parameter + Member + MaybeSerializeDebugButNotDeserialize + Default + traits::Digest<Hash = Self::Hash>;
	type AccountId: Parameter + Member + MaybeSerializeDebug + MaybeDisplay + Ord + Default;
	type Header: Parameter + traits::Header<
		Number = Self::BlockNumber,
		Hash = Self::Hash,
		Digest = Self::Digest
	>;
	type Event: Parameter + Member + From<Event>;
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

/// Event for the system module.
decl_event!(
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

decl_storage! {
	trait Store for Module<T: Trait> as System {

		pub AccountNonce get(account_nonce): map T::AccountId => T::Index;

		ExtrinsicCount: Option<u32>;
		pub BlockHash get(block_hash) build(|_| vec![(T::BlockNumber::zero(), [69u8; 32])]): map T::BlockNumber => T::Hash;
		ExtrinsicData get(extrinsic_data): map u32 => Vec<u8>;
		RandomSeed get(random_seed) build(|_| [0u8; 32]): T::Hash;
		/// The current block number being processed. Set by `execute_block`.
		Number get(block_number) build(|_| 1u64): T::BlockNumber;
		ParentHash get(parent_hash) build(|_| [69u8; 32]): T::Hash;
		ExtrinsicsRoot get(extrinsics_root): T::Hash;
		Digest get(digest): T::Digest;

		Events get(events): Vec<EventRecord<T::Event>>;
	}
	add_extra_genesis {
		config(changes_trie_config): Option<ChangesTrieConfiguration>;

		build(|storage: &mut primitives::StorageMap, _: &mut primitives::ChildrenStorageMap, config: &GenesisConfig<T>| {
			use codec::Encode;

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

	/// Start the execution of a particular block.
	pub fn initialise(number: &T::BlockNumber, parent_hash: &T::Hash, txs_root: &T::Hash) {
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
	pub fn finalise() -> T::Header {
		<RandomSeed<T>>::kill();
		<ExtrinsicCount<T>>::kill();

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

		<T::Header as traits::Header>::new(number, extrinsics_root, storage_root,
			parent_hash, digest)
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
			twox_128(&<BlockHash<T>>::key_for(T::BlockNumber::zero())).to_vec() => [69u8; 32].encode(),	// TODO: replace with Hash::default().encode
			twox_128(<Number<T>>::key()).to_vec() => T::BlockNumber::one().encode(),
			twox_128(<ParentHash<T>>::key()).to_vec() => [69u8; 32].encode(),	// TODO: replace with Hash::default().encode
			twox_128(<RandomSeed<T>>::key()).to_vec() => T::Hash::default().encode()
		])
	}

	/// Set the block number to something in particular. Can be used as an alternative to
	/// `initialise` for tests that don't need to bother with the other environment entries.
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
	/// `initialise` for tests that don't need to bother with the other environment entries.
	#[cfg(any(feature = "std", test))]
	pub fn set_parent_hash(n: T::Hash) {
		<ParentHash<T>>::put(n);
	}

	/// Set the random seed to something in particular. Can be used as an alternative to
	/// `initialise` for tests that don't need to bother with the other environment entries.
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
	pub fn note_extrinsic(encoded_xt: Vec<u8>) {
		<ExtrinsicData<T>>::insert(Self::extrinsic_index().unwrap_or_default(), encoded_xt);
	}

	/// To be called immediately after an extrinsic has been applied.
	pub fn note_applied_extrinsic(r: &Result<(), &'static str>) {
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
	type Source = T::AccountId;
	type Target = T::AccountId;
	fn lookup(&self, s: Self::Source) -> rstd::result::Result<Self::Target, &'static str> {
		Ok(s)
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
	use primitives::traits::BlakeTwo256;
	use primitives::testing::{Digest, DigestItem, Header};

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
			System::initialise(&1, &[0u8; 32].into(), &[0u8; 32].into());
			System::note_finished_extrinsics();
			System::deposit_event(1u16);
			System::finalise();
			assert_eq!(System::events(), vec![EventRecord { phase: Phase::Finalization, event: 1u16 }]);

			System::initialise(&2, &[0u8; 32].into(), &[0u8; 32].into());
			System::deposit_event(42u16);
			System::note_applied_extrinsic(&Ok(()));
			System::note_applied_extrinsic(&Err(""));
			System::note_finished_extrinsics();
			System::deposit_event(3u16);
			System::finalise();
			assert_eq!(System::events(), vec![
				EventRecord { phase: Phase::ApplyExtrinsic(0), event: 42u16 },
				EventRecord { phase: Phase::ApplyExtrinsic(0), event: 100u16 },
				EventRecord { phase: Phase::ApplyExtrinsic(1), event: 101u16 },
				EventRecord { phase: Phase::Finalization, event: 3u16 }
			]);
		});
	}
}
