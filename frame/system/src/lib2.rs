// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! TODO module docs

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
		Dispatchable, AtLeast32BitUnsigned, Saturating,
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
		extract_actual_weight, PerDispatchClass,
	},
	dispatch::DispatchResultWithPostInfo,
};
use codec::{Encode, Decode, FullCodec, EncodeLike};

#[cfg(any(feature = "std", test))]
use sp_io::TestExternalities;

pub mod offchain;
pub mod limits;
#[cfg(test)]
pub(crate) mod mock;

mod extensions;
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

/// An object to track the currently used extrinsic weight in a block.
pub type ConsumedWeight = PerDispatchClass<Weight>;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	/// System configuration trait. Implemented by runtime.
	pub trait Config: 'static + Eq + Clone {
		/// The basic call filter to use in Origin. All origins are built with this filter as base,
		/// except Root.
		type BaseCallFilter: Filter<Self::Call>;

		/// Block & extrinsics weights: base values and limits.
		#[pallet::constant]
		type BlockWeights: Get<limits::BlockWeights>;

		/// The maximum length of a block (in bytes).
		type BlockLength: Get<limits::BlockLength>;

		/// The `Origin` type used by dispatchable calls.
		type Origin:
			Into<Result<RawOrigin<Self::AccountId>, Self::Origin>>
			+ From<RawOrigin<Self::AccountId>>
			+ Clone
			+ OriginTrait<Call=Self::Call>;

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
		type Hashing: Hash<Output=Self::Hash>;

		/// The user account identifier type for the runtime.
		type AccountId: Parameter + Member + MaybeSerializeDeserialize + Debug + MaybeDisplay + Ord
			+ Default;

		/// Converting trait to take a source type and convert to `AccountId`.
		///
		/// Used to define the type and conversion mechanism for referencing accounts in transactions.
		/// It's perfectly reasonable for this to be an identity conversion (with the source type being
		/// `AccountId`), but other modules (e.g. Indices module) may provide more functional/efficient
		/// alternatives.
		type Lookup: StaticLookup<Target=Self::AccountId>;

		/// The block header.
		type Header: Parameter + traits::Header<
			Number=Self::BlockNumber,
			Hash=Self::Hash,
		>;

		/// The aggregated event type of the runtime.
		type Event: Parameter + Member + From<Event<Self>> + Debug;

		/// Maximum number of block number to block hash mappings to keep (oldest pruned first).
		#[pallet::constant]
		type BlockHashCount: Get<Self::BlockNumber>;

		/// The weight of runtime database operations the runtime can invoke.
		#[pallet::constant]
		type DbWeight: Get<RuntimeDbWeight>;

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

		/// The designated SS85 prefix of this chain.
		///
		/// This replaces the "ss58Format" property declared in the chain spec. Reason is
		/// that the runtime should know about the prefix in order to make use of it as
		/// an identifier of the chain.
		#[pallet::constant]
		type SS58Prefix: Get<u8>;
	}


	#[pallet::pallet]
	#[pallet::generate_store(pub (super) trait Store)]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::hooks]
	impl<T: Trait> Hooks for Pallet<T> {
		fn on_runtime_upgrade() -> frame_support::weights::Weight {
			if !UpgradedToU32RefCount::get() {
				Account::<T>::translate::<(T::Index, u8, T::AccountData), _>(|_key, (nonce, rc, data)|
					Some(AccountInfo { nonce, refcount: rc as RefCount, data })
				);
				UpgradedToU32RefCount::put(true);
				T::BlockWeights::get().max_block
			} else {
				0
			}
		}

		fn integrity_test() {
			T::BlockWeights::get()
				.validate()
				.expect("The weights are invalid.");
		}
	}

	#[pallet::interface]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T>
	// TODO_MAYBE_WHERE_CLAUSE
	{
		// TODO_ON_FINALIZE
		// TODO_ON_INITIALIZE
		// TODO_ON_RUNTIME_UPGRADE
		// TODO_INTEGRITY_TEST
		// TODO_OFFCHAIN_WORKER
	}

	#[pallet::call]
	impl<T: Config> Pallet<T>
	// TODO_MAYBE_WHERE_CLAUSE
	{
		// TODO_UPGRADE_DISPATCHABLES
	}

	#[pallet::inherent]
	// TODO_INHERENT
	#[pallet::event]
	#[pallet::generate_deposit(pub (super) fn deposit_event)]
	// TODO_EVENT

	// TODO_REMOVE_IF_NO_EVENT
	/// Old name generated by `decl_event`.
	#[deprecated(note = "use `Event` instead")]
	pub type RawEvent = Event;

	#[pallet::error]
	// TODO_ERROR
	#[pallet::origin]
	// TODO_ORIGIN
	#[pallet::validate_unsigned]
	// TODO_VALIDATE_UNSIGNED
	/// The full account information for a particular account ID.
	#[pallet::storage]
	#[pallet::getter(fn account)]
	pub type Account<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		AccountInfo<T::Index, T::AccountData>,
		ValueQuery,
	>;

	/// Total extrinsics count for the current block.
	#[pallet::storage]
	pub(super) type ExtrinsicCount<T: Config> = StorageValue<_, u32>;

	/// The current weight for the block.
	#[pallet::storage]
	#[pallet::getter(fn block_weight)]
	pub(super) type BlockWeight<T: Config> = StorageValue<_, ConsumedWeight, ValueQuery>;

	/// Total length (in bytes) for all extrinsics put together, for the current block.
	#[pallet::storage]
	pub(super) type AllExtrinsicsLen<T: Config> = StorageValue<_, u32>;

	/// Map of block numbers to block hashes.
	#[pallet::storage]
	#[pallet::getter(fn block_hash)]
	pub type BlockHash<T: Config> =
	StorageMap<_, Twox64Concat, T::BlockNumber, T::Hash, ValueQuery>;

	/// Extrinsics data for the current block (maps an extrinsic's index to its data).
	#[pallet::storage]
	#[pallet::getter(fn extrinsic_data)]
	pub(super) type ExtrinsicData<T: Config> =
	StorageMap<_, Twox64Concat, u32, Vec<u8>, ValueQuery>;

	/// The current block number being processed. Set by `execute_block`.
	#[pallet::storage]
	#[pallet::getter(fn block_number)]
	pub(super) type Number<T: Config> = StorageValue<_, T::BlockNumber, ValueQuery>;

	/// Hash of the previous block.
	#[pallet::storage]
	#[pallet::getter(fn parent_hash)]
	pub(super) type ParentHash<T: Config> = StorageValue<_, T::Hash, ValueQuery>;

	/// Digest of the current block, also part of the block header.
	#[pallet::storage]
	#[pallet::getter(fn digest)]
	pub(super) type Digest<T: Config> = StorageValue<_, DigestOf<T>, ValueQuery>;

	/// Events deposited for the current block.
	#[pallet::storage]
	#[pallet::getter(fn events)]
	pub(super) type Events<T: Config> =
	StorageValue<_, Vec<EventRecord<T::Event, T::Hash>>, ValueQuery>;

	/// The number of events in the `Events<T>` list.
	#[pallet::storage]
	#[pallet::getter(fn event_count)]
	pub(super) type EventCount<T: Config> = StorageValue<_, EventIndex, ValueQuery>;

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
	#[pallet::storage]
	#[pallet::getter(fn event_topics)]
	pub(super) type EventTopics<T: Config> =
	StorageMap<_, Blake2_128Concat, T::Hash, Vec<(T::BlockNumber, EventIndex)>, ValueQuery>;

	/// Stores the `spec_version` and `spec_name` of when the last runtime upgrade happened.
	#[pallet::storage]
	pub type LastRuntimeUpgrade<T: Config> = StorageValue<_, LastRuntimeUpgradeInfo>;

	/// True if we have upgraded so that `type RefCount` is `u32`. False (default) if not.
	#[pallet::storage]
	pub(super) type UpgradedToU32RefCount<T: Config> = StorageValue<_, bool, ValueQuery>;

	/// The execution phase of the block.
	#[pallet::storage]
	pub(super) type ExecutionPhase<T: Config> = StorageValue<_, Phase>;

	#[pallet::genesis_config]
	pub struct GenesisConfig
// TODO_MAYBE_WHERE_CLAUSE
	{
		pub changes_trie_config: Option<ChangesTrieConfiguration>,
		#[serde(with = "sp_core::bytes")]
		pub code: Vec<u8>,
	}

	#[cfg(feature = "std")]
	impl Default for GenesisConfig
	// TODO_MAYBE_WHERE_CLAUSE
	{
		fn default() -> Self {
			Self {
				changes_trie_config: Default::default(),
				code: Default::default(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig
	// TODO_MAYBE_WHERE_CLAUSE
	{
		fn build(&self) {
			{
				let builder: fn(&Self) -> _ = |_| vec![(T::BlockNumber::zero(), hash69())];
				let data = &builder(self);
				let data: &frame_support::sp_std::vec::Vec<(T::BlockNumber, T::Hash)> = data;
				data.iter().for_each(|(k, v)| {
					<BlockHash<T, > as frame_support::storage::StorageMap
					<T::BlockNumber, T::Hash>>::insert::<&T::
					BlockNumber, &T::Hash>(k, v);
				});
			}
			{
				let builder: fn(&Self) -> _ = |_| hash69();
				let data = &builder(self);
				let v: &T::Hash = data;
				<ParentHash<T> as frame_support::storage::StorageValue<T::Hash>>::put::<&T::Hash>(
					v,
				);
			}
			{
				let builder: fn(&Self) -> _ =
					|_| Some(LastRuntimeUpgradeInfo::from(T::Version::get()));
				let data = builder(self);
				let data = Option::as_ref(&data);
				let v: Option<&LastRuntimeUpgradeInfo> = data;
				if let Some(v) = v {
					<LastRuntimeUpgrade as frame_support::storage::StorageValue<
						LastRuntimeUpgradeInfo,
					>>::put::<&LastRuntimeUpgradeInfo>(v);
				}
			}
			{
				let builder: fn(&Self) -> _ = |_| true;
				let data = &builder(self);
				let v: &bool = data;
				<UpgradedToU32RefCount as frame_support::storage::StorageValue<bool>>::put::<&bool>(
					v,
				);
			}
			let extra_genesis_builder: fn(&Self) = |config: &GenesisConfig| {
				use codec::Encode;
				sp_io::storage::set(well_known_keys::CODE, &config.code);
				sp_io::storage::set(well_known_keys::EXTRINSIC_INDEX, &0u32.encode());
				if let Some(ref changes_trie_config) = config.changes_trie_config {
					sp_io::storage::set(
						well_known_keys::CHANGES_TRIE_CONFIG,
						&changes_trie_config.encode(),
					);
				}
			};
			extra_genesis_builder(self);
		}
	}
}
