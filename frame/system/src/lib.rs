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

	/// System configuration trait. Implemented by runtime.
	#[pallet::config]
	#[pallet::disable_frame_system_supertrait_check]
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
		type Event: Parameter + Member + From<Event<Self>> + Debug + IsType<<Self as frame_system::Config>::Event>;

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
	impl<T: Config> Hooks for Pallet<T> {
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

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// A dispatch that will fill the block weight up to the given ratio.
		// TODO: This should only be available for testing, rather than in general usage, but
		// that's not possible at present (since it's within the decl_module macro).
		#[weight(*_ratio * T::BlockWeights::get().max_block)]
		fn fill_block(origin: OriginFor<T>, _ratio: Perbill) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			Ok(().into())
		}

		/// Make some on-chain remark.
		///
		/// # <weight>
		/// - `O(1)`
		/// - Base Weight: 0.665 µs, independent of remark length.
		/// - No DB operations.
		/// # </weight>
		#[weight(T::SystemWeightInfo::remark(_remark.len() as u32))]
		fn remark(origin: OriginFor<T>, _remark: Vec<u8>) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?;
			Ok(().into())
		}

		/// Set the number of pages in the WebAssembly environment's heap.
		///
		/// # <weight>
		/// - `O(1)`
		/// - 1 storage write.
		/// - Base Weight: 1.405 µs
		/// - 1 write to HEAP_PAGES
		/// # </weight>
		#[weight((T::SystemWeightInfo::set_heap_pages(), DispatchClass::Operational))]
		fn set_heap_pages(origin: OriginFor<T>, pages: u64) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			storage::unhashed::put_raw(well_known_keys::HEAP_PAGES, &pages.encode());
			Ok(().into())
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
		#[weight((T::BlockWeights::get().max_block, DispatchClass::Operational))]
		pub fn set_code(origin: OriginFor<T>, code: Vec<u8>) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			Self::can_set_code(&code)?;

			storage::unhashed::put_raw(well_known_keys::CODE, &code);
			Self::deposit_event(RawEvent::CodeUpdated);
			Ok(().into())
		}

		/// Set the new runtime code without doing any checks of the given `code`.
		///
		/// # <weight>
		/// - `O(C)` where `C` length of `code`
		/// - 1 storage write (codec `O(C)`).
		/// - 1 event.
		/// The weight of this function is dependent on the runtime. We will treat this as a full block.
		/// # </weight>
		#[weight((T::BlockWeights::get().max_block, DispatchClass::Operational))]
		pub fn set_code_without_checks(
			origin: OriginFor<T>,
			code: Vec<u8>
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			storage::unhashed::put_raw(well_known_keys::CODE, &code);
			Self::deposit_event(RawEvent::CodeUpdated);
			Ok(().into())
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
		#[weight((T::SystemWeightInfo::set_changes_trie_config(), DispatchClass::Operational))]
		pub fn set_changes_trie_config(
			origin: OriginFor<T>,
			changes_trie_config: Option<ChangesTrieConfiguration>
		) -> DispatchResultWithPostInfo {
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
			Ok(().into())
		}

		/// Set some items of storage.
		///
		/// # <weight>
		/// - `O(I)` where `I` length of `items`
		/// - `I` storage writes (`O(1)`).
		/// - Base Weight: 0.568 * i µs
		/// - Writes: Number of items
		/// # </weight>
		#[weight((
			T::SystemWeightInfo::set_storage(items.len() as u32),
			DispatchClass::Operational,
		))]
		fn set_storage(origin: OriginFor<T>, items: Vec<KeyValue>) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			for i in &items {
				storage::unhashed::put_raw(&i.0, &i.1);
			}
			Ok(().into())
		}

		/// Kill some items from storage.
		///
		/// # <weight>
		/// - `O(IK)` where `I` length of `keys` and `K` length of one key
		/// - `I` storage deletions.
		/// - Base Weight: .378 * i µs
		/// - Writes: Number of items
		/// # </weight>
		#[weight((
			T::SystemWeightInfo::kill_storage(keys.len() as u32),
			DispatchClass::Operational,
		))]
		fn kill_storage(origin: OriginFor<T>, keys: Vec<Key>) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			for key in &keys {
				storage::unhashed::kill(&key);
			}
			Ok(().into())
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
		#[weight((
			T::SystemWeightInfo::kill_prefix(_subkeys.saturating_add(1)),
			DispatchClass::Operational,
		))]
		fn kill_prefix(
			origin: OriginFor<T>,
			prefix: Key,
			_subkeys: u32
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			storage::unhashed::kill_prefix(&prefix);
			Ok(().into())
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
		#[weight((T::SystemWeightInfo::suicide(), DispatchClass::Operational))]
		pub fn suicide(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let account = Account::<T>::get(&who);
			ensure!(account.refcount == 0, Error::<T>::NonZeroRefCount);
			ensure!(account.data == T::AccountData::default(), Error::<T>::NonDefaultComposite);
			Self::kill_account(&who);
			Ok(().into())
		}
	}

	/// Event for the System module.
	#[pallet::event]
	pub enum Event<T: Config> {
		/// An extrinsic completed successfully. \[info\]
		ExtrinsicSuccess(DispatchInfo),
		/// An extrinsic failed. \[error, info\]
		ExtrinsicFailed(DispatchError, DispatchInfo),
		/// `:code` was updated.
		CodeUpdated,
		/// A new \[account\] was created.
		NewAccount(T::AccountId),
		/// An \[account\] was reaped.
		KilledAccount(T::AccountId),
	}

	/// Old name generated by `decl_event`.
	#[deprecated(note = "use `Event` instead")]
	pub type RawEvent<T: Config> = Event<T>;

	/// Error for the System module
	#[pallet::error]
	pub enum Error {
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

	/// Exposed trait-generic origin type.
	#[pallet::origin]
	pub type Origin<T> = RawOrigin<<T as Config>::AccountId>;

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
	pub struct GenesisConfig {
		pub changes_trie_config: Option<ChangesTrieConfiguration>,
		#[serde(with = "sp_core::bytes")]
		pub code: Vec<u8>,
	}

	#[cfg(feature = "std")]
	impl Default for GenesisConfig {
		fn default() -> Self {
			Self {
				changes_trie_config: Default::default(),
				code: Default::default(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
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
