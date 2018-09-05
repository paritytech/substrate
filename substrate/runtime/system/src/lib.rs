// Copyright 2017 Parity Technologies (UK) Ltd.
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

#[cfg(any(feature = "std", test))]
extern crate substrate_primitives;

#[cfg_attr(any(feature = "std", test), macro_use)]
extern crate substrate_runtime_std as rstd;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

#[cfg(feature = "std")]
extern crate serde;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate substrate_codec_derive;

extern crate substrate_codec as codec;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_primitives as primitives;
extern crate safe_mix;

use rstd::prelude::*;
use primitives::traits::{self, CheckEqual, SimpleArithmetic, SimpleBitOps, Zero, One, Bounded,
	Hash, Member, MaybeDisplay, RefInto, MaybeEmpty};
use runtime_support::{StorageValue, StorageMap, Parameter};
use safe_mix::TripletMix;

#[cfg(any(feature = "std", test))]
use rstd::marker::PhantomData;
#[cfg(any(feature = "std", test))]
use codec::Encode;

#[cfg(any(feature = "std", test))]
use runtime_io::{twox_128, TestExternalities, KeccakHasher};

/// Compute the extrinsics root of a list of extrinsics.
pub fn extrinsics_root<H: Hash, E: codec::Encode>(extrinsics: &[E]) -> H::Output {
	extrinsics_data_root::<H>(extrinsics.iter().map(codec::Encode::encode).collect())
}

/// Compute the extrinsics root of a list of extrinsics.
pub fn extrinsics_data_root<H: Hash>(xts: Vec<Vec<u8>>) -> H::Output {
	let xts = xts.iter().map(Vec::as_slice).collect::<Vec<_>>();
	H::enumerated_trie_root(&xts)
}

pub trait Trait: Eq + Clone {
	// We require that PublicAux impl MaybeEmpty, since we require that inherents - or unsigned
	// user-level extrinsics - can exist.
	type PublicAux: RefInto<Self::AccountId> + MaybeEmpty;
	type Index: Parameter + Member + Default + MaybeDisplay + SimpleArithmetic + Copy;
	type BlockNumber: Parameter + Member + MaybeDisplay + SimpleArithmetic + Default + Bounded + Copy + rstd::hash::Hash;
	type Hash: Parameter + Member + MaybeDisplay + SimpleBitOps + Default + Copy + CheckEqual + rstd::hash::Hash + AsRef<[u8]>;
	type Hashing: Hash<Output = Self::Hash>;
	type Digest: Parameter + Member + Default + traits::Digest;
	type AccountId: Parameter + Member + MaybeDisplay + Ord + Default;
	type Header: Parameter + traits::Header<
		Number = Self::BlockNumber,
		Hash = Self::Hash,
		Digest = Self::Digest
	>;
	type Event: Parameter + Member + From<Event>;
}

pub type DigestItemOf<T> = <<T as Trait>::Digest as traits::Digest>::Item;

decl_module! {
	pub struct Module<T: Trait>;
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
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub enum Event {
	/// An extrinsic completed successfully.
	ExtrinsicSuccess,
	/// An extrinsic failed.
	ExtrinsicFailed,
}

impl From<Event> for () {
	fn from(_: Event) -> () { () }
}

decl_storage! {
	trait Store for Module<T: Trait> as System {

		pub AccountNonce get(account_nonce): default map [ T::AccountId => T::Index ];

		ExtrinsicCount: u32;
		pub BlockHash get(block_hash): required map [ T::BlockNumber => T::Hash ];
		pub ExtrinsicIndex get(extrinsic_index): u32;
		ExtrinsicData get(extrinsic_data): required map [ u32 => Vec<u8> ];
		RandomSeed get(random_seed): required T::Hash;
		/// The current block number being processed. Set by `execute_block`.
		Number get(block_number): required T::BlockNumber;
		ParentHash get(parent_hash): required T::Hash;
		ExtrinsicsRoot get(extrinsics_root): required T::Hash;
		Digest get(digest): default T::Digest;

		Events get(events): default Vec<EventRecord<T::Event>>;
	}
}

impl<T: Trait> Module<T> {
	/// Start the execution of a particular block.
	pub fn initialise(number: &T::BlockNumber, parent_hash: &T::Hash, txs_root: &T::Hash) {
		// populate environment.
		<Number<T>>::put(number);
		<ParentHash<T>>::put(parent_hash);
		<BlockHash<T>>::insert(*number - One::one(), parent_hash);
		<ExtrinsicsRoot<T>>::put(txs_root);
		<RandomSeed<T>>::put(Self::calculate_random());
		<ExtrinsicIndex<T>>::put(0u32);
		<Events<T>>::kill();
	}

	/// Remove temporary "environment" entries in storage.
	pub fn finalise() -> T::Header {
		<RandomSeed<T>>::kill();
		<ExtrinsicCount<T>>::kill();

		let number = <Number<T>>::take();
		let parent_hash = <ParentHash<T>>::take();
		let digest = <Digest<T>>::take();
		let extrinsics_root = <ExtrinsicsRoot<T>>::take();
		let storage_root = T::Hashing::storage_root();

		// <Events<T>> stays to be inspected by the client.

		<T::Header as traits::Header>::new(number, extrinsics_root, storage_root, parent_hash, digest)
	}

	/// Deposits a log and ensures it matches the blocks log data.
	pub fn deposit_log(item: <T::Digest as traits::Digest>::Item) {
		let mut l = <Digest<T>>::get();
		traits::Digest::push(&mut l, item);
		<Digest<T>>::put(l);
	}

	/// Deposits an event onto this block's event record.
	pub fn deposit_event(event: T::Event) {
		let phase = <ExtrinsicIndex<T>>::get().map_or(Phase::Finalization, |c| Phase::ApplyExtrinsic(c));
		let mut events = Self::events();
		events.push(EventRecord { phase, event });
		<Events<T>>::put(events);
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
	pub fn externalities() -> TestExternalities<KeccakHasher> {
		map![
			twox_128(&<BlockHash<T>>::key_for(T::BlockNumber::zero())).to_vec() => [69u8; 32].encode(),	// TODO: replace with Hash::default().encode
			twox_128(<Number<T>>::key()).to_vec() => T::BlockNumber::one().encode(),
			twox_128(<ParentHash<T>>::key()).to_vec() => [69u8; 32].encode(),	// TODO: replace with Hash::default().encode
			twox_128(<RandomSeed<T>>::key()).to_vec() => T::Hash::default().encode()
		]
	}

	/// Set the block number to something in particular. Can be used as an alternative to
	/// `initialise` for tests that don't need to bother with the other environment entries.
	#[cfg(any(feature = "std", test))]
	pub fn set_block_number(n: T::BlockNumber) {
		<Number<T>>::put(n);
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
		<ExtrinsicData<T>>::insert(<ExtrinsicIndex<T>>::get().unwrap_or_default(), encoded_xt);
	}

	/// To be called immediately after an extrinsic has been applied.
	pub fn note_applied_extrinsic(r: &Result<(), &'static str>) {
		Self::deposit_event(match r {
			Ok(_) => Event::ExtrinsicSuccess,
			Err(_) => Event::ExtrinsicFailed,
		}.into());
		<ExtrinsicIndex<T>>::put(<ExtrinsicIndex<T>>::get().unwrap_or_default() + 1u32);
	}

	/// To be called immediately after `note_applied_extrinsic` of the last extrinsic of the block
	/// has been called.
	pub fn note_finished_extrinsics() {
		<ExtrinsicCount<T>>::put(<ExtrinsicIndex<T>>::get().unwrap_or_default());
		<ExtrinsicIndex<T>>::kill();
	}

	/// Remove all extrinsics data and save the extrinsics trie root.
	pub fn derive_extrinsics() {
		let extrinsics = (0..<ExtrinsicCount<T>>::get().unwrap_or_default()).map(<ExtrinsicData<T>>::take).collect();
		let xts_root = extrinsics_data_root::<T::Hashing>(extrinsics);
		<ExtrinsicsRoot<T>>::put(xts_root);
	}
}

#[cfg(any(feature = "std", test))]
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct GenesisConfig<T: Trait>(PhantomData<T>);

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig(PhantomData)
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> primitives::BuildStorage for GenesisConfig<T>
{
	fn build_storage(self) -> Result<primitives::StorageMap, String> {
		use codec::Encode;

		Ok(map![
			Self::hash(&<BlockHash<T>>::key_for(T::BlockNumber::zero())).to_vec() => [69u8; 32].encode(),
			Self::hash(<Number<T>>::key()).to_vec() => 1u64.encode(),
			Self::hash(<ParentHash<T>>::key()).to_vec() => [69u8; 32].encode(),
			Self::hash(<RandomSeed<T>>::key()).to_vec() => [0u8; 32].encode(),
			Self::hash(<ExtrinsicIndex<T>>::key()).to_vec() => [0u8; 4].encode()
		])
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::with_externalities;
	use substrate_primitives::H256;
	use primitives::BuildStorage;
	use primitives::traits::BlakeTwo256;
	use primitives::testing::{Digest, Header};

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl Trait for Test {
		type PublicAux = u64;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
		type Event = u16;
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

	fn new_test_ext() -> runtime_io::TestExternalities<KeccakHasher> {
		GenesisConfig::<Test>::default().build_storage().unwrap().into()
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
