// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! # System Pallet
//!
//! The System pallet provides low-level access to core types and cross-cutting utilities.
//! It acts as the base layer for other pallets to interact with the Substrate framework components.
//!
//! - [`Config`]
//!
//! ## Overview
//!
//! The System pallet defines the core data types used in a Substrate runtime.
//! It also provides several utility functions (see [`Pallet`]) for other FRAME pallets.
//!
//! In addition, it manages the storage items for extrinsics data, indexes, event records, and
//! digest items, among other things that support the execution of the current block.
//!
//! It also handles low-level tasks like depositing logs, basic set up and take down of
//! temporary storage entries, and access to previous block hashes.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! The System pallet does not implement any dispatchable functions.
//!
//! ### Public Functions
//!
//! See the [`Pallet`] struct for details of publicly available functions.
//!
//! ### Signed Extensions
//!
//! The System pallet defines the following extensions:
//!
//!   - [`CheckWeight`]: Checks the weight and length of the block and ensure that it does not
//!     exceed the limits.
//!   - [`CheckNonce`]: Checks the nonce of the transaction. Contains a single payload of type
//!     `T::Index`.
//!   - [`CheckEra`]: Checks the era of the transaction. Contains a single payload of type `Era`.
//!   - [`CheckGenesis`]: Checks the provided genesis hash of the transaction. Must be a part of the
//!     signed payload of the transaction.
//!   - [`CheckSpecVersion`]: Checks that the runtime version is the same as the one used to sign
//!     the transaction.
//!   - [`CheckTxVersion`]: Checks that the transaction version is the same as the one used to sign
//!     the transaction.
//!
//! Lookup the runtime aggregator file (e.g. `node/runtime`) to see the full list of signed
//! extensions included in a chain.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::Serialize;
use sp_io::hashing::blake2_256;
#[cfg(feature = "runtime-benchmarks")]
use sp_runtime::traits::TrailingZeroInput;
use sp_runtime::{
	generic,
	traits::{
		self, AtLeast32Bit, AtLeast32BitUnsigned, BadOrigin, BlockNumberProvider, Bounded,
		CheckEqual, Dispatchable, Hash, Lookup, LookupError, MaybeDisplay,
		MaybeSerializeDeserialize, Member, One, Saturating, SimpleBitOps, StaticLookup, Zero,
	},
	DispatchError, RuntimeDebug,
};
#[cfg(any(feature = "std", test))]
use sp_std::map;
use sp_std::{fmt::Debug, marker::PhantomData, prelude::*};
use sp_version::RuntimeVersion;

use codec::{Decode, Encode, EncodeLike, FullCodec, MaxEncodedLen};
use frame_support::{
	dispatch::{
		extract_actual_pays_fee, extract_actual_weight, DispatchClass, DispatchInfo,
		DispatchResult, DispatchResultWithPostInfo, PerDispatchClass,
	},
	impl_ensure_origin_with_arg_ignoring_arg,
	storage::{self, StorageStreamIter},
	traits::{
		ConstU32, Contains, EnsureOrigin, EnsureOriginWithArg, Get, HandleLifetime,
		OnKilledAccount, OnNewAccount, OriginTrait, PalletInfo, SortedMembers, StoredMap, TypedGet,
	},
	Parameter,
};
use scale_info::TypeInfo;
use sp_core::storage::well_known_keys;
use sp_weights::{RuntimeDbWeight, Weight};

#[cfg(feature = "std")]
use frame_support::traits::GenesisBuild;
#[cfg(any(feature = "std", test))]
use sp_io::TestExternalities;

pub mod limits;
#[cfg(test)]
pub(crate) mod mock;
pub mod offchain;

mod extensions;
#[cfg(feature = "std")]
pub mod mocking;
#[cfg(test)]
mod tests;
pub mod weights;

pub mod migrations;

pub use extensions::{
	check_genesis::CheckGenesis, check_mortality::CheckMortality,
	check_non_zero_sender::CheckNonZeroSender, check_nonce::CheckNonce,
	check_spec_version::CheckSpecVersion, check_tx_version::CheckTxVersion,
	check_weight::CheckWeight,
};
// Backward compatible re-export.
pub use extensions::check_mortality::CheckMortality as CheckEra;
pub use frame_support::dispatch::RawOrigin;
pub use weights::WeightInfo;

const LOG_TARGET: &str = "runtime::system";

/// Compute the trie root of a list of extrinsics.
///
/// The merkle proof is using the same trie as runtime state with
/// `state_version` 0.
pub fn extrinsics_root<H: Hash, E: codec::Encode>(extrinsics: &[E]) -> H::Output {
	extrinsics_data_root::<H>(extrinsics.iter().map(codec::Encode::encode).collect())
}

/// Compute the trie root of a list of extrinsics.
///
/// The merkle proof is using the same trie as runtime state with
/// `state_version` 0.
pub fn extrinsics_data_root<H: Hash>(xts: Vec<Vec<u8>>) -> H::Output {
	H::ordered_trie_root(xts, sp_core::storage::StateVersion::V0)
}

/// An object to track the currently used extrinsic weight in a block.
pub type ConsumedWeight = PerDispatchClass<Weight>;

pub use pallet::*;

/// Do something when we should be setting the code.
pub trait SetCode<T: Config> {
	/// Set the code to the given blob.
	fn set_code(code: Vec<u8>) -> DispatchResult;
}

impl<T: Config> SetCode<T> for () {
	fn set_code(code: Vec<u8>) -> DispatchResult {
		<Pallet<T>>::update_code_in_storage(&code)?;
		Ok(())
	}
}

/// Numeric limits over the ability to add a consumer ref using `inc_consumers`.
pub trait ConsumerLimits {
	/// The number of consumers over which `inc_consumers` will cease to work.
	fn max_consumers() -> RefCount;
	/// The maximum number of additional consumers expected to be over be added at once using
	/// `inc_consumers_without_limit`.
	///
	/// Note: This is not enforced and it's up to the chain's author to ensure this reflects the
	/// actual situation.
	fn max_overflow() -> RefCount;
}

impl<const Z: u32> ConsumerLimits for ConstU32<Z> {
	fn max_consumers() -> RefCount {
		Z
	}
	fn max_overflow() -> RefCount {
		Z
	}
}

impl<MaxNormal: Get<u32>, MaxOverflow: Get<u32>> ConsumerLimits for (MaxNormal, MaxOverflow) {
	fn max_consumers() -> RefCount {
		MaxNormal::get()
	}
	fn max_overflow() -> RefCount {
		MaxOverflow::get()
	}
}

#[frame_support::pallet]
pub mod pallet {
	use crate::{self as frame_system, pallet_prelude::*, *};
	use frame_support::pallet_prelude::*;

	/// Contains default types suitable for various environments
	pub mod config_preludes {
		use super::DefaultConfig;

		/// Provides a viable default config that can be used with
		/// [`derive_impl`](`frame_support::derive_impl`) to derive a testing pallet config
		/// based on this one.
		///
		/// See `Test` in the `default-config` example pallet's `test.rs` for an example of
		/// a downstream user of this particular `TestDefaultConfig`
		pub struct TestDefaultConfig;

		#[frame_support::register_default_impl(TestDefaultConfig)]
		impl DefaultConfig for TestDefaultConfig {
			type Index = u32;
			type BlockNumber = u32;
			type Header = sp_runtime::generic::Header<Self::BlockNumber, Self::Hashing>;
			type Hash = sp_core::hash::H256;
			type Hashing = sp_runtime::traits::BlakeTwo256;
			type AccountId = u64;
			type Lookup = sp_runtime::traits::IdentityLookup<u64>;
			type BlockHashCount = frame_support::traits::ConstU32<10>;
			type MaxConsumers = frame_support::traits::ConstU32<16>;
			type AccountData = ();
			type OnNewAccount = ();
			type OnKilledAccount = ();
			type SystemWeightInfo = ();
			type SS58Prefix = ();
			type Version = ();
			type BlockWeights = ();
			type BlockLength = ();
			type DbWeight = ();
		}
	}

	/// System configuration trait. Implemented by runtime.
	#[pallet::config(with_default)]
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config: 'static + Eq + Clone {
		/// The aggregated event type of the runtime.
		type RuntimeEvent: Parameter
			+ Member
			+ From<Event<Self>>
			+ Debug
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The basic call filter to use in Origin. All origins are built with this filter as base,
		/// except Root.
		#[pallet::no_default]
		type BaseCallFilter: Contains<Self::RuntimeCall>;

		/// Block & extrinsics weights: base values and limits.
		#[pallet::constant]
		type BlockWeights: Get<limits::BlockWeights>;

		/// The maximum length of a block (in bytes).
		#[pallet::constant]
		type BlockLength: Get<limits::BlockLength>;

		/// The `RuntimeOrigin` type used by dispatchable calls.
		#[pallet::no_default]
		type RuntimeOrigin: Into<Result<RawOrigin<Self::AccountId>, Self::RuntimeOrigin>>
			+ From<RawOrigin<Self::AccountId>>
			+ Clone
			+ OriginTrait<Call = Self::RuntimeCall, AccountId = Self::AccountId>;

		/// The aggregated `RuntimeCall` type.
		#[pallet::no_default]
		type RuntimeCall: Parameter
			+ Dispatchable<RuntimeOrigin = Self::RuntimeOrigin>
			+ Debug
			+ From<Call<Self>>;

		/// Account index (aka nonce) type. This stores the number of previous transactions
		/// associated with a sender account.
		type Index: Parameter
			+ Member
			+ MaybeSerializeDeserialize
			+ Debug
			+ Default
			+ MaybeDisplay
			+ AtLeast32Bit
			+ Copy
			+ MaxEncodedLen;

		/// The block number type used by the runtime.
		type BlockNumber: Parameter
			+ Member
			+ MaybeSerializeDeserialize
			+ Debug
			+ MaybeDisplay
			+ AtLeast32BitUnsigned
			+ Default
			+ Bounded
			+ Copy
			+ sp_std::hash::Hash
			+ sp_std::str::FromStr
			+ MaxEncodedLen
			+ TypeInfo;

		/// The output of the `Hashing` function.
		type Hash: Parameter
			+ Member
			+ MaybeSerializeDeserialize
			+ Debug
			+ MaybeDisplay
			+ SimpleBitOps
			+ Ord
			+ Default
			+ Copy
			+ CheckEqual
			+ sp_std::hash::Hash
			+ AsRef<[u8]>
			+ AsMut<[u8]>
			+ MaxEncodedLen;

		/// The hashing system (algorithm) being used in the runtime (e.g. Blake2).
		type Hashing: Hash<Output = Self::Hash> + TypeInfo;

		/// The user account identifier type for the runtime.
		type AccountId: Parameter
			+ Member
			+ MaybeSerializeDeserialize
			+ Debug
			+ MaybeDisplay
			+ Ord
			+ MaxEncodedLen;

		/// Converting trait to take a source type and convert to `AccountId`.
		///
		/// Used to define the type and conversion mechanism for referencing accounts in
		/// transactions. It's perfectly reasonable for this to be an identity conversion (with the
		/// source type being `AccountId`), but other pallets (e.g. Indices pallet) may provide more
		/// functional/efficient alternatives.
		type Lookup: StaticLookup<Target = Self::AccountId>;

		/// The block header.
		type Header: Parameter + traits::Header<Number = Self::BlockNumber, Hash = Self::Hash>;

		/// Maximum number of block number to block hash mappings to keep (oldest pruned first).
		#[pallet::constant]
		type BlockHashCount: Get<Self::BlockNumber>;

		/// The weight of runtime database operations the runtime can invoke.
		#[pallet::constant]
		type DbWeight: Get<RuntimeDbWeight>;

		/// Get the chain's current version.
		#[pallet::constant]
		type Version: Get<RuntimeVersion>;

		/// Provides information about the pallet setup in the runtime.
		///
		/// Expects the `PalletInfo` type that is being generated by `construct_runtime!` in the
		/// runtime.
		///
		/// For tests it is okay to use `()` as type, however it will provide "useless" data.
		#[pallet::no_default]
		type PalletInfo: PalletInfo;

		/// Data to be associated with an account (other than nonce/transaction counter, which this
		/// pallet does regardless).
		type AccountData: Member + FullCodec + Clone + Default + TypeInfo + MaxEncodedLen;

		/// Handler for when a new account has just been created.
		type OnNewAccount: OnNewAccount<Self::AccountId>;

		/// A function that is invoked when an account has been determined to be dead.
		///
		/// All resources should be cleaned up associated with the given account.
		type OnKilledAccount: OnKilledAccount<Self::AccountId>;

		type SystemWeightInfo: WeightInfo;

		/// The designated SS58 prefix of this chain.
		///
		/// This replaces the "ss58Format" property declared in the chain spec. Reason is
		/// that the runtime should know about the prefix in order to make use of it as
		/// an identifier of the chain.
		#[pallet::constant]
		type SS58Prefix: Get<u16>;

		/// What to do if the runtime wants to change the code to something new.
		///
		/// The default (`()`) implementation is responsible for setting the correct storage
		/// entry and emitting corresponding event and log item. (see
		/// [`Pallet::update_code_in_storage`]).
		/// It's unlikely that this needs to be customized, unless you are writing a parachain using
		/// `Cumulus`, where the actual code change is deferred.
		#[pallet::no_default]
		type OnSetCode: SetCode<Self>;

		/// The maximum number of consumers allowed on a single account.
		type MaxConsumers: ConsumerLimits;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		#[cfg(feature = "std")]
		fn integrity_test() {
			sp_io::TestExternalities::default().execute_with(|| {
				T::BlockWeights::get().validate().expect("The weights are invalid.");
			});
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Make some on-chain remark.
		///
		/// Can be executed by every `origin`.
		#[pallet::call_index(0)]
		#[pallet::weight(T::SystemWeightInfo::remark(_remark.len() as u32))]
		pub fn remark(_origin: OriginFor<T>, _remark: Vec<u8>) -> DispatchResultWithPostInfo {
			Ok(().into())
		}

		/// Set the number of pages in the WebAssembly environment's heap.
		#[pallet::call_index(1)]
		#[pallet::weight((T::SystemWeightInfo::set_heap_pages(), DispatchClass::Operational))]
		pub fn set_heap_pages(origin: OriginFor<T>, pages: u64) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			storage::unhashed::put_raw(well_known_keys::HEAP_PAGES, &pages.encode());
			Self::deposit_log(generic::DigestItem::RuntimeEnvironmentUpdated);
			Ok(().into())
		}

		/// Set the new runtime code.
		#[pallet::call_index(2)]
		#[pallet::weight((T::SystemWeightInfo::set_code(), DispatchClass::Operational))]
		pub fn set_code(origin: OriginFor<T>, code: Vec<u8>) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			Self::can_set_code(&code)?;
			T::OnSetCode::set_code(code)?;
			// consume the rest of the block to prevent further transactions
			Ok(Some(T::BlockWeights::get().max_block).into())
		}

		/// Set the new runtime code without doing any checks of the given `code`.
		#[pallet::call_index(3)]
		#[pallet::weight((T::SystemWeightInfo::set_code(), DispatchClass::Operational))]
		pub fn set_code_without_checks(
			origin: OriginFor<T>,
			code: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			T::OnSetCode::set_code(code)?;
			Ok(Some(T::BlockWeights::get().max_block).into())
		}

		/// Set some items of storage.
		#[pallet::call_index(4)]
		#[pallet::weight((
			T::SystemWeightInfo::set_storage(items.len() as u32),
			DispatchClass::Operational,
		))]
		pub fn set_storage(
			origin: OriginFor<T>,
			items: Vec<KeyValue>,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			for i in &items {
				storage::unhashed::put_raw(&i.0, &i.1);
			}
			Ok(().into())
		}

		/// Kill some items from storage.
		#[pallet::call_index(5)]
		#[pallet::weight((
			T::SystemWeightInfo::kill_storage(keys.len() as u32),
			DispatchClass::Operational,
		))]
		pub fn kill_storage(origin: OriginFor<T>, keys: Vec<Key>) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			for key in &keys {
				storage::unhashed::kill(key);
			}
			Ok(().into())
		}

		/// Kill all storage items with a key that starts with the given prefix.
		///
		/// **NOTE:** We rely on the Root origin to provide us the number of subkeys under
		/// the prefix we are removing to accurately calculate the weight of this function.
		#[pallet::call_index(6)]
		#[pallet::weight((
			T::SystemWeightInfo::kill_prefix(_subkeys.saturating_add(1)),
			DispatchClass::Operational,
		))]
		pub fn kill_prefix(
			origin: OriginFor<T>,
			prefix: Key,
			_subkeys: u32,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			let _ = storage::unhashed::clear_prefix(&prefix, None, None);
			Ok(().into())
		}

		/// Make some on-chain remark and emit event.
		#[pallet::call_index(7)]
		#[pallet::weight(T::SystemWeightInfo::remark_with_event(remark.len() as u32))]
		pub fn remark_with_event(
			origin: OriginFor<T>,
			remark: Vec<u8>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let hash = T::Hashing::hash(&remark[..]);
			Self::deposit_event(Event::Remarked { sender: who, hash });
			Ok(().into())
		}
	}

	/// Event for the System pallet.
	#[pallet::event]
	pub enum Event<T: Config> {
		/// An extrinsic completed successfully.
		ExtrinsicSuccess { dispatch_info: DispatchInfo },
		/// An extrinsic failed.
		ExtrinsicFailed { dispatch_error: DispatchError, dispatch_info: DispatchInfo },
		/// `:code` was updated.
		CodeUpdated,
		/// A new account was created.
		NewAccount { account: T::AccountId },
		/// An account was reaped.
		KilledAccount { account: T::AccountId },
		/// On on-chain remark happened.
		Remarked { sender: T::AccountId, hash: T::Hash },
	}

	/// Error for the System pallet
	#[pallet::error]
	pub enum Error<T> {
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
		/// The origin filter prevent the call to be dispatched.
		CallFiltered,
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
	#[pallet::whitelist_storage]
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
	#[pallet::unbounded]
	pub(super) type ExtrinsicData<T: Config> =
		StorageMap<_, Twox64Concat, u32, Vec<u8>, ValueQuery>;

	/// The current block number being processed. Set by `execute_block`.
	#[pallet::storage]
	#[pallet::whitelist_storage]
	#[pallet::getter(fn block_number)]
	pub(super) type Number<T: Config> = StorageValue<_, T::BlockNumber, ValueQuery>;

	/// Hash of the previous block.
	#[pallet::storage]
	#[pallet::getter(fn parent_hash)]
	pub(super) type ParentHash<T: Config> = StorageValue<_, T::Hash, ValueQuery>;

	/// Digest of the current block, also part of the block header.
	#[pallet::storage]
	#[pallet::unbounded]
	#[pallet::getter(fn digest)]
	pub(super) type Digest<T: Config> = StorageValue<_, generic::Digest, ValueQuery>;

	/// Events deposited for the current block.
	///
	/// NOTE: The item is unbound and should therefore never be read on chain.
	/// It could otherwise inflate the PoV size of a block.
	///
	/// Events have a large in-memory size. Box the events to not go out-of-memory
	/// just in case someone still reads them from within the runtime.
	#[pallet::storage]
	#[pallet::whitelist_storage]
	#[pallet::unbounded]
	pub(super) type Events<T: Config> =
		StorageValue<_, Vec<Box<EventRecord<T::RuntimeEvent, T::Hash>>>, ValueQuery>;

	/// The number of events in the `Events<T>` list.
	#[pallet::storage]
	#[pallet::whitelist_storage]
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
	#[pallet::unbounded]
	#[pallet::getter(fn event_topics)]
	pub(super) type EventTopics<T: Config> =
		StorageMap<_, Blake2_128Concat, T::Hash, Vec<(T::BlockNumber, EventIndex)>, ValueQuery>;

	/// Stores the `spec_version` and `spec_name` of when the last runtime upgrade happened.
	#[pallet::storage]
	#[pallet::unbounded]
	pub type LastRuntimeUpgrade<T: Config> = StorageValue<_, LastRuntimeUpgradeInfo>;

	/// True if we have upgraded so that `type RefCount` is `u32`. False (default) if not.
	#[pallet::storage]
	pub(super) type UpgradedToU32RefCount<T: Config> = StorageValue<_, bool, ValueQuery>;

	/// True if we have upgraded so that AccountInfo contains three types of `RefCount`. False
	/// (default) if not.
	#[pallet::storage]
	pub(super) type UpgradedToTripleRefCount<T: Config> = StorageValue<_, bool, ValueQuery>;

	/// The execution phase of the block.
	#[pallet::storage]
	#[pallet::whitelist_storage]
	pub(super) type ExecutionPhase<T: Config> = StorageValue<_, Phase>;

	#[derive(Default)]
	#[pallet::genesis_config]
	pub struct GenesisConfig {
		#[serde(with = "sp_core::bytes")]
		pub code: Vec<u8>,
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			<BlockHash<T>>::insert::<_, T::Hash>(T::BlockNumber::zero(), hash69());
			<ParentHash<T>>::put::<T::Hash>(hash69());
			<LastRuntimeUpgrade<T>>::put(LastRuntimeUpgradeInfo::from(T::Version::get()));
			<UpgradedToU32RefCount<T>>::put(true);
			<UpgradedToTripleRefCount<T>>::put(true);

			sp_io::storage::set(well_known_keys::CODE, &self.code);
			sp_io::storage::set(well_known_keys::EXTRINSIC_INDEX, &0u32.encode());
		}
	}
}

#[cfg(feature = "std")]
impl GenesisConfig {
	/// Direct implementation of `GenesisBuild::build_storage`.
	///
	/// Kept in order not to break dependency.
	pub fn build_storage<T: Config>(&self) -> Result<sp_runtime::Storage, String> {
		<Self as GenesisBuild<T>>::build_storage(self)
	}

	/// Direct implementation of `GenesisBuild::assimilate_storage`.
	///
	/// Kept in order not to break dependency.
	pub fn assimilate_storage<T: Config>(
		&self,
		storage: &mut sp_runtime::Storage,
	) -> Result<(), String> {
		<Self as GenesisBuild<T>>::assimilate_storage(self, storage)
	}
}

pub type Key = Vec<u8>;
pub type KeyValue = (Vec<u8>, Vec<u8>);

/// A phase of a block's execution.
#[derive(Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
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
#[derive(Encode, Decode, RuntimeDebug, TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, PartialEq, Eq, Clone))]
pub struct EventRecord<E: Parameter + Member, T> {
	/// The phase of the block it happened in.
	pub phase: Phase,
	/// The event itself.
	pub event: E,
	/// The list of the topics this event has.
	pub topics: Vec<T>,
}

// Create a Hash with 69 for each byte,
// only used to build genesis config.
fn hash69<T: AsMut<[u8]> + Default>() -> T {
	let mut h = T::default();
	h.as_mut().iter_mut().for_each(|byte| *byte = 69);
	h
}

/// This type alias represents an index of an event.
///
/// We use `u32` here because this index is used as index for `Events<T>`
/// which can't contain more than `u32::MAX` items.
type EventIndex = u32;

/// Type used to encode the number of references an account has.
pub type RefCount = u32;

/// Information of an account.
#[derive(Clone, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct AccountInfo<Index, AccountData> {
	/// The number of transactions this account has sent.
	pub nonce: Index,
	/// The number of other modules that currently depend on this account's existence. The account
	/// cannot be reaped until this is zero.
	pub consumers: RefCount,
	/// The number of other modules that allow this account to exist. The account may not be reaped
	/// until this and `sufficients` are both zero.
	pub providers: RefCount,
	/// The number of modules that allow this account to exist for their own purposes only. The
	/// account may not be reaped until this and `providers` are both zero.
	pub sufficients: RefCount,
	/// The additional data that belongs to this account. Used to store the balance(s) in a lot of
	/// chains.
	pub data: AccountData,
}

/// Stores the `spec_version` and `spec_name` of when the last runtime upgrade
/// happened.
#[derive(sp_runtime::RuntimeDebug, Encode, Decode, TypeInfo)]
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
		Self { spec_version: version.spec_version.into(), spec_name: version.spec_name }
	}
}

/// Ensure the origin is Root.
pub struct EnsureRoot<AccountId>(sp_std::marker::PhantomData<AccountId>);
impl<O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>, AccountId>
	EnsureOrigin<O> for EnsureRoot<AccountId>
{
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Root => Ok(()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		Ok(O::from(RawOrigin::Root))
	}
}

impl_ensure_origin_with_arg_ignoring_arg! {
	impl< { O: .., AccountId: Decode, T } >
		EnsureOriginWithArg<O, T> for EnsureRoot<AccountId>
	{}
}

/// Ensure the origin is Root and return the provided `Success` value.
pub struct EnsureRootWithSuccess<AccountId, Success>(
	sp_std::marker::PhantomData<(AccountId, Success)>,
);
impl<
		O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
		AccountId,
		Success: TypedGet,
	> EnsureOrigin<O> for EnsureRootWithSuccess<AccountId, Success>
{
	type Success = Success::Type;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Root => Ok(Success::get()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		Ok(O::from(RawOrigin::Root))
	}
}

impl_ensure_origin_with_arg_ignoring_arg! {
	impl< { O: .., AccountId: Decode, Success: TypedGet, T } >
		EnsureOriginWithArg<O, T> for EnsureRootWithSuccess<AccountId, Success>
	{}
}

/// Ensure the origin is provided `Ensure` origin and return the provided `Success` value.
pub struct EnsureWithSuccess<Ensure, AccountId, Success>(
	sp_std::marker::PhantomData<(Ensure, AccountId, Success)>,
);

impl<
		O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
		Ensure: EnsureOrigin<O>,
		AccountId,
		Success: TypedGet,
	> EnsureOrigin<O> for EnsureWithSuccess<Ensure, AccountId, Success>
{
	type Success = Success::Type;

	fn try_origin(o: O) -> Result<Self::Success, O> {
		Ensure::try_origin(o).map(|_| Success::get())
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		Ensure::try_successful_origin()
	}
}

/// Ensure the origin is any `Signed` origin.
pub struct EnsureSigned<AccountId>(sp_std::marker::PhantomData<AccountId>);
impl<O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>, AccountId: Decode>
	EnsureOrigin<O> for EnsureSigned<AccountId>
{
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Signed(who) => Ok(who),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		let zero_account_id =
			AccountId::decode(&mut TrailingZeroInput::zeroes()).map_err(|_| ())?;
		Ok(O::from(RawOrigin::Signed(zero_account_id)))
	}
}

impl_ensure_origin_with_arg_ignoring_arg! {
	impl< { O: .., AccountId: Decode, T } >
		EnsureOriginWithArg<O, T> for EnsureSigned<AccountId>
	{}
}

/// Ensure the origin is `Signed` origin from the given `AccountId`.
pub struct EnsureSignedBy<Who, AccountId>(sp_std::marker::PhantomData<(Who, AccountId)>);
impl<
		O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
		Who: SortedMembers<AccountId>,
		AccountId: PartialEq + Clone + Ord + Decode,
	> EnsureOrigin<O> for EnsureSignedBy<Who, AccountId>
{
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Signed(ref who) if Who::contains(who) => Ok(who.clone()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		let first_member = match Who::sorted_members().first() {
			Some(account) => account.clone(),
			None => AccountId::decode(&mut TrailingZeroInput::zeroes()).map_err(|_| ())?,
		};
		Ok(O::from(RawOrigin::Signed(first_member)))
	}
}

impl_ensure_origin_with_arg_ignoring_arg! {
	impl< { O: .., Who: SortedMembers<AccountId>, AccountId: PartialEq + Clone + Ord + Decode, T } >
		EnsureOriginWithArg<O, T> for EnsureSignedBy<Who, AccountId>
	{}
}

/// Ensure the origin is `None`. i.e. unsigned transaction.
pub struct EnsureNone<AccountId>(sp_std::marker::PhantomData<AccountId>);
impl<O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>, AccountId>
	EnsureOrigin<O> for EnsureNone<AccountId>
{
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::None => Ok(()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		Ok(O::from(RawOrigin::None))
	}
}

impl_ensure_origin_with_arg_ignoring_arg! {
	impl< { O: .., AccountId, T } >
		EnsureOriginWithArg<O, T> for EnsureNone<AccountId>
	{}
}

/// Always fail.
pub struct EnsureNever<Success>(sp_std::marker::PhantomData<Success>);
impl<O, Success> EnsureOrigin<O> for EnsureNever<Success> {
	type Success = Success;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		Err(o)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		Err(())
	}
}

impl_ensure_origin_with_arg_ignoring_arg! {
	impl< { O, Success, T } >
		EnsureOriginWithArg<O, T> for EnsureNever<Success>
	{}
}

/// Ensure that the origin `o` represents a signed extrinsic (i.e. transaction).
/// Returns `Ok` with the account that signed the extrinsic or an `Err` otherwise.
pub fn ensure_signed<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<AccountId, BadOrigin>
where
	OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>,
{
	match o.into() {
		Ok(RawOrigin::Signed(t)) => Ok(t),
		_ => Err(BadOrigin),
	}
}

/// Ensure that the origin `o` represents either a signed extrinsic (i.e. transaction) or the root.
/// Returns `Ok` with the account that signed the extrinsic, `None` if it was root,  or an `Err`
/// otherwise.
pub fn ensure_signed_or_root<OuterOrigin, AccountId>(
	o: OuterOrigin,
) -> Result<Option<AccountId>, BadOrigin>
where
	OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>,
{
	match o.into() {
		Ok(RawOrigin::Root) => Ok(None),
		Ok(RawOrigin::Signed(t)) => Ok(Some(t)),
		_ => Err(BadOrigin),
	}
}

/// Ensure that the origin `o` represents the root. Returns `Ok` or an `Err` otherwise.
pub fn ensure_root<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), BadOrigin>
where
	OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>,
{
	match o.into() {
		Ok(RawOrigin::Root) => Ok(()),
		_ => Err(BadOrigin),
	}
}

/// Ensure that the origin `o` represents an unsigned extrinsic. Returns `Ok` or an `Err` otherwise.
pub fn ensure_none<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), BadOrigin>
where
	OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>,
{
	match o.into() {
		Ok(RawOrigin::None) => Ok(()),
		_ => Err(BadOrigin),
	}
}

/// Reference status; can be either referenced or unreferenced.
#[derive(RuntimeDebug)]
pub enum RefStatus {
	Referenced,
	Unreferenced,
}

/// Some resultant status relevant to incrementing a provider/self-sufficient reference.
#[derive(Eq, PartialEq, RuntimeDebug)]
pub enum IncRefStatus {
	/// Account was created.
	Created,
	/// Account already existed.
	Existed,
}

/// Some resultant status relevant to decrementing a provider/self-sufficient reference.
#[derive(Eq, PartialEq, RuntimeDebug)]
pub enum DecRefStatus {
	/// Account was destroyed.
	Reaped,
	/// Account still exists.
	Exists,
}

impl<T: Config> Pallet<T> {
	pub fn account_exists(who: &T::AccountId) -> bool {
		Account::<T>::contains_key(who)
	}

	/// Write code to the storage and emit related events and digest items.
	///
	/// Note this function almost never should be used directly. It is exposed
	/// for `OnSetCode` implementations that defer actual code being written to
	/// the storage (for instance in case of parachains).
	pub fn update_code_in_storage(code: &[u8]) -> DispatchResult {
		storage::unhashed::put_raw(well_known_keys::CODE, code);
		Self::deposit_log(generic::DigestItem::RuntimeEnvironmentUpdated);
		Self::deposit_event(Event::CodeUpdated);
		Ok(())
	}

	/// Increment the reference counter on an account.
	#[deprecated = "Use `inc_consumers` instead"]
	pub fn inc_ref(who: &T::AccountId) {
		let _ = Self::inc_consumers(who);
	}

	/// Decrement the reference counter on an account. This *MUST* only be done once for every time
	/// you called `inc_consumers` on `who`.
	#[deprecated = "Use `dec_consumers` instead"]
	pub fn dec_ref(who: &T::AccountId) {
		let _ = Self::dec_consumers(who);
	}

	/// The number of outstanding references for the account `who`.
	#[deprecated = "Use `consumers` instead"]
	pub fn refs(who: &T::AccountId) -> RefCount {
		Self::consumers(who)
	}

	/// True if the account has no outstanding references.
	#[deprecated = "Use `!is_provider_required` instead"]
	pub fn allow_death(who: &T::AccountId) -> bool {
		!Self::is_provider_required(who)
	}

	/// Increment the provider reference counter on an account.
	pub fn inc_providers(who: &T::AccountId) -> IncRefStatus {
		Account::<T>::mutate(who, |a| {
			if a.providers == 0 && a.sufficients == 0 {
				// Account is being created.
				a.providers = 1;
				Self::on_created_account(who.clone(), a);
				IncRefStatus::Created
			} else {
				a.providers = a.providers.saturating_add(1);
				IncRefStatus::Existed
			}
		})
	}

	/// Decrement the provider reference counter on an account.
	///
	/// This *MUST* only be done once for every time you called `inc_providers` on `who`.
	pub fn dec_providers(who: &T::AccountId) -> Result<DecRefStatus, DispatchError> {
		Account::<T>::try_mutate_exists(who, |maybe_account| {
			if let Some(mut account) = maybe_account.take() {
				if account.providers == 0 {
					// Logic error - cannot decrement beyond zero.
					log::error!(
						target: LOG_TARGET,
						"Logic error: Unexpected underflow in reducing provider",
					);
					account.providers = 1;
				}
				match (account.providers, account.consumers, account.sufficients) {
					(1, 0, 0) => {
						// No providers left (and no consumers) and no sufficients. Account dead.

						Pallet::<T>::on_killed_account(who.clone());
						Ok(DecRefStatus::Reaped)
					},
					(1, c, _) if c > 0 => {
						// Cannot remove last provider if there are consumers.
						Err(DispatchError::ConsumerRemaining)
					},
					(x, _, _) => {
						// Account will continue to exist as there is either > 1 provider or
						// > 0 sufficients.
						account.providers = x - 1;
						*maybe_account = Some(account);
						Ok(DecRefStatus::Exists)
					},
				}
			} else {
				log::error!(
					target: LOG_TARGET,
					"Logic error: Account already dead when reducing provider",
				);
				Ok(DecRefStatus::Reaped)
			}
		})
	}

	/// Increment the self-sufficient reference counter on an account.
	pub fn inc_sufficients(who: &T::AccountId) -> IncRefStatus {
		Account::<T>::mutate(who, |a| {
			if a.providers + a.sufficients == 0 {
				// Account is being created.
				a.sufficients = 1;
				Self::on_created_account(who.clone(), a);
				IncRefStatus::Created
			} else {
				a.sufficients = a.sufficients.saturating_add(1);
				IncRefStatus::Existed
			}
		})
	}

	/// Decrement the sufficients reference counter on an account.
	///
	/// This *MUST* only be done once for every time you called `inc_sufficients` on `who`.
	pub fn dec_sufficients(who: &T::AccountId) -> DecRefStatus {
		Account::<T>::mutate_exists(who, |maybe_account| {
			if let Some(mut account) = maybe_account.take() {
				if account.sufficients == 0 {
					// Logic error - cannot decrement beyond zero.
					log::error!(
						target: LOG_TARGET,
						"Logic error: Unexpected underflow in reducing sufficients",
					);
				}
				match (account.sufficients, account.providers) {
					(0, 0) | (1, 0) => {
						Pallet::<T>::on_killed_account(who.clone());
						DecRefStatus::Reaped
					},
					(x, _) => {
						account.sufficients = x - 1;
						*maybe_account = Some(account);
						DecRefStatus::Exists
					},
				}
			} else {
				log::error!(
					target: LOG_TARGET,
					"Logic error: Account already dead when reducing provider",
				);
				DecRefStatus::Reaped
			}
		})
	}

	/// The number of outstanding provider references for the account `who`.
	pub fn providers(who: &T::AccountId) -> RefCount {
		Account::<T>::get(who).providers
	}

	/// The number of outstanding sufficient references for the account `who`.
	pub fn sufficients(who: &T::AccountId) -> RefCount {
		Account::<T>::get(who).sufficients
	}

	/// The number of outstanding provider and sufficient references for the account `who`.
	pub fn reference_count(who: &T::AccountId) -> RefCount {
		let a = Account::<T>::get(who);
		a.providers + a.sufficients
	}

	/// Increment the reference counter on an account.
	///
	/// The account `who`'s `providers` must be non-zero and the current number of consumers must
	/// be less than `MaxConsumers::max_consumers()` or this will return an error.
	pub fn inc_consumers(who: &T::AccountId) -> Result<(), DispatchError> {
		Account::<T>::try_mutate(who, |a| {
			if a.providers > 0 {
				if a.consumers < T::MaxConsumers::max_consumers() {
					a.consumers = a.consumers.saturating_add(1);
					Ok(())
				} else {
					Err(DispatchError::TooManyConsumers)
				}
			} else {
				Err(DispatchError::NoProviders)
			}
		})
	}

	/// Increment the reference counter on an account, ignoring the `MaxConsumers` limits.
	///
	/// The account `who`'s `providers` must be non-zero or this will return an error.
	pub fn inc_consumers_without_limit(who: &T::AccountId) -> Result<(), DispatchError> {
		Account::<T>::try_mutate(who, |a| {
			if a.providers > 0 {
				a.consumers = a.consumers.saturating_add(1);
				Ok(())
			} else {
				Err(DispatchError::NoProviders)
			}
		})
	}

	/// Decrement the reference counter on an account. This *MUST* only be done once for every time
	/// you called `inc_consumers` on `who`.
	pub fn dec_consumers(who: &T::AccountId) {
		Account::<T>::mutate(who, |a| {
			if a.consumers > 0 {
				a.consumers -= 1;
			} else {
				log::error!(
					target: LOG_TARGET,
					"Logic error: Unexpected underflow in reducing consumer",
				);
			}
		})
	}

	/// The number of outstanding references for the account `who`.
	pub fn consumers(who: &T::AccountId) -> RefCount {
		Account::<T>::get(who).consumers
	}

	/// True if the account has some outstanding consumer references.
	pub fn is_provider_required(who: &T::AccountId) -> bool {
		Account::<T>::get(who).consumers != 0
	}

	/// True if the account has no outstanding consumer references or more than one provider.
	pub fn can_dec_provider(who: &T::AccountId) -> bool {
		let a = Account::<T>::get(who);
		a.consumers == 0 || a.providers > 1
	}

	/// True if the account has at least one provider reference and adding `amount` consumer
	/// references would not take it above the the maximum.
	pub fn can_accrue_consumers(who: &T::AccountId, amount: u32) -> bool {
		let a = Account::<T>::get(who);
		match a.consumers.checked_add(amount) {
			Some(c) => a.providers > 0 && c <= T::MaxConsumers::max_consumers(),
			None => false,
		}
	}

	/// True if the account has at least one provider reference and fewer consumer references than
	/// the maximum.
	pub fn can_inc_consumer(who: &T::AccountId) -> bool {
		Self::can_accrue_consumers(who, 1)
	}

	/// Deposits an event into this block's event record.
	///
	/// NOTE: Events not registered at the genesis block and quietly omitted.
	pub fn deposit_event(event: impl Into<T::RuntimeEvent>) {
		Self::deposit_event_indexed(&[], event.into());
	}

	/// Deposits an event into this block's event record adding this event
	/// to the corresponding topic indexes.
	///
	/// This will update storage entries that correspond to the specified topics.
	/// It is expected that light-clients could subscribe to this topics.
	///
	/// NOTE: Events not registered at the genesis block and quietly omitted.
	pub fn deposit_event_indexed(topics: &[T::Hash], event: T::RuntimeEvent) {
		let block_number = Self::block_number();
		// Don't populate events on genesis.
		if block_number.is_zero() {
			return
		}

		let phase = ExecutionPhase::<T>::get().unwrap_or_default();
		let event = EventRecord { phase, event, topics: topics.to_vec() };

		// Index of the to be added event.
		let event_idx = {
			let old_event_count = EventCount::<T>::get();
			let new_event_count = match old_event_count.checked_add(1) {
				// We've reached the maximum number of events at this block, just
				// don't do anything and leave the event_count unaltered.
				None => return,
				Some(nc) => nc,
			};
			EventCount::<T>::put(new_event_count);
			old_event_count
		};

		Events::<T>::append(event);

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
		ExtrinsicCount::<T>::get().unwrap_or_default()
	}

	pub fn all_extrinsics_len() -> u32 {
		AllExtrinsicsLen::<T>::get().unwrap_or_default()
	}

	/// Inform the system pallet of some additional weight that should be accounted for, in the
	/// current block.
	///
	/// NOTE: use with extra care; this function is made public only be used for certain pallets
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
		BlockWeight::<T>::mutate(|current_weight| {
			current_weight.accrue(weight, class);
		});
	}

	/// Start the execution of a particular block.
	pub fn initialize(number: &T::BlockNumber, parent_hash: &T::Hash, digest: &generic::Digest) {
		// populate environment
		ExecutionPhase::<T>::put(Phase::Initialization);
		storage::unhashed::put(well_known_keys::EXTRINSIC_INDEX, &0u32);
		let entropy = (b"frame_system::initialize", parent_hash).using_encoded(blake2_256);
		storage::unhashed::put_raw(well_known_keys::INTRABLOCK_ENTROPY, &entropy[..]);
		<Number<T>>::put(number);
		<Digest<T>>::put(digest);
		<ParentHash<T>>::put(parent_hash);
		<BlockHash<T>>::insert(*number - One::one(), parent_hash);

		// Remove previous block data from storage
		BlockWeight::<T>::kill();
	}

	/// Remove temporary "environment" entries in storage, compute the storage root and return the
	/// resulting header for this block.
	pub fn finalize() -> T::Header {
		log::debug!(
			target: LOG_TARGET,
			"[{:?}] {} extrinsics, length: {} (normal {}%, op: {}%, mandatory {}%) / normal weight:\
			 {} ({}%) op weight {} ({}%) / mandatory weight {} ({}%)",
			Self::block_number(),
			Self::extrinsic_index().unwrap_or_default(),
			Self::all_extrinsics_len(),
			sp_runtime::Percent::from_rational(
				Self::all_extrinsics_len(),
				*T::BlockLength::get().max.get(DispatchClass::Normal)
			).deconstruct(),
			sp_runtime::Percent::from_rational(
				Self::all_extrinsics_len(),
				*T::BlockLength::get().max.get(DispatchClass::Operational)
			).deconstruct(),
			sp_runtime::Percent::from_rational(
				Self::all_extrinsics_len(),
				*T::BlockLength::get().max.get(DispatchClass::Mandatory)
			).deconstruct(),
			Self::block_weight().get(DispatchClass::Normal),
			sp_runtime::Percent::from_rational(
				Self::block_weight().get(DispatchClass::Normal).ref_time(),
				T::BlockWeights::get().get(DispatchClass::Normal).max_total.unwrap_or(Bounded::max_value()).ref_time()
			).deconstruct(),
			Self::block_weight().get(DispatchClass::Operational),
			sp_runtime::Percent::from_rational(
				Self::block_weight().get(DispatchClass::Operational).ref_time(),
				T::BlockWeights::get().get(DispatchClass::Operational).max_total.unwrap_or(Bounded::max_value()).ref_time()
			).deconstruct(),
			Self::block_weight().get(DispatchClass::Mandatory),
			sp_runtime::Percent::from_rational(
				Self::block_weight().get(DispatchClass::Mandatory).ref_time(),
				T::BlockWeights::get().get(DispatchClass::Mandatory).max_total.unwrap_or(Bounded::max_value()).ref_time()
			).deconstruct(),
		);
		ExecutionPhase::<T>::kill();
		AllExtrinsicsLen::<T>::kill();
		storage::unhashed::kill(well_known_keys::INTRABLOCK_ENTROPY);

		// The following fields
		//
		// - <Events<T>>
		// - <EventCount<T>>
		// - <EventTopics<T>>
		// - <Number<T>>
		// - <ParentHash<T>>
		// - <Digest<T>>
		//
		// stay to be inspected by the client and will be cleared by `Self::initialize`.
		let number = <Number<T>>::get();
		let parent_hash = <ParentHash<T>>::get();
		let digest = <Digest<T>>::get();

		let extrinsics = (0..ExtrinsicCount::<T>::take().unwrap_or_default())
			.map(ExtrinsicData::<T>::take)
			.collect();
		let extrinsics_root = extrinsics_data_root::<T::Hashing>(extrinsics);

		// move block hash pruning window by one block
		let block_hash_count = T::BlockHashCount::get();
		let to_remove = number.saturating_sub(block_hash_count).saturating_sub(One::one());

		// keep genesis hash
		if !to_remove.is_zero() {
			<BlockHash<T>>::remove(to_remove);
		}

		let version = T::Version::get().state_version();
		let storage_root = T::Hash::decode(&mut &sp_io::storage::root(version)[..])
			.expect("Node is configured to use the same hash; qed");

		<T::Header as traits::Header>::new(
			number,
			extrinsics_root,
			storage_root,
			parent_hash,
			digest,
		)
	}

	/// Deposits a log and ensures it matches the block's log data.
	pub fn deposit_log(item: generic::DigestItem) {
		<Digest<T>>::append(item);
	}

	/// Get the basic externalities for this pallet, useful for tests.
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

	/// Get the current events deposited by the runtime.
	///
	/// NOTE: This should only be used in tests. Reading events from the runtime can have a large
	/// impact on the PoV size of a block. Users should use alternative and well bounded storage
	/// items for any behavior like this.
	///
	/// NOTE: Events not registered at the genesis block and quietly omitted.
	#[cfg(any(feature = "std", feature = "runtime-benchmarks", test))]
	pub fn events() -> Vec<EventRecord<T::RuntimeEvent, T::Hash>> {
		debug_assert!(
			!Self::block_number().is_zero(),
			"events not registered at the genesis block"
		);
		// Dereferencing the events here is fine since we are not in the
		// memory-restricted runtime.
		Self::read_events_no_consensus().map(|e| *e).collect()
	}

	/// Get a single event at specified index.
	///
	/// Should only be called if you know what you are doing and outside of the runtime block
	/// execution else it can have a large impact on the PoV size of a block.
	pub fn event_no_consensus(index: usize) -> Option<T::RuntimeEvent> {
		Self::read_events_no_consensus().nth(index).map(|e| e.event.clone())
	}

	/// Get the current events deposited by the runtime.
	///
	/// Should only be called if you know what you are doing and outside of the runtime block
	/// execution else it can have a large impact on the PoV size of a block.
	pub fn read_events_no_consensus(
	) -> impl sp_std::iter::Iterator<Item = Box<EventRecord<T::RuntimeEvent, T::Hash>>> {
		Events::<T>::stream_iter()
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
	pub fn set_block_consumed_resources(weight: Weight, len: usize) {
		BlockWeight::<T>::mutate(|current_weight| {
			current_weight.set(weight, DispatchClass::Normal)
		});
		AllExtrinsicsLen::<T>::put(len as u32);
	}

	/// Reset events.
	///
	/// This needs to be used in prior calling [`initialize`](Self::initialize) for each new block
	/// to clear events from previous block.
	pub fn reset_events() {
		<Events<T>>::kill();
		EventCount::<T>::kill();
		let _ = <EventTopics<T>>::clear(u32::max_value(), None);
	}

	/// Assert the given `event` exists.
	///
	/// NOTE: Events not registered at the genesis block and quietly omitted.
	#[cfg(any(feature = "std", feature = "runtime-benchmarks", test))]
	pub fn assert_has_event(event: T::RuntimeEvent) {
		let events = Self::events();
		assert!(
			events.iter().any(|record| record.event == event),
			"expected event {event:?} not found in events {events:?}",
		);
	}

	/// Assert the last event equal to the given `event`.
	///
	/// NOTE: Events not registered at the genesis block and quietly omitted.
	#[cfg(any(feature = "std", feature = "runtime-benchmarks", test))]
	pub fn assert_last_event(event: T::RuntimeEvent) {
		let last_event = Self::events().last().expect("events expected").event.clone();
		assert_eq!(
			last_event, event,
			"expected event {event:?} is not equal to the last event {last_event:?}",
		);
	}

	/// Return the chain's current runtime version.
	pub fn runtime_version() -> RuntimeVersion {
		T::Version::get()
	}

	/// Retrieve the account transaction counter from storage.
	pub fn account_nonce(who: impl EncodeLike<T::AccountId>) -> T::Index {
		Account::<T>::get(who).nonce
	}

	/// Increment a particular account's nonce by 1.
	pub fn inc_account_nonce(who: impl EncodeLike<T::AccountId>) {
		Account::<T>::mutate(who, |a| a.nonce += T::Index::one());
	}

	/// Note what the extrinsic data of the current extrinsic index is.
	///
	/// This is required to be called before applying an extrinsic. The data will used
	/// in [`Self::finalize`] to calculate the correct extrinsics root.
	pub fn note_extrinsic(encoded_xt: Vec<u8>) {
		ExtrinsicData::<T>::insert(Self::extrinsic_index().unwrap_or_default(), encoded_xt);
	}

	/// To be called immediately after an extrinsic has been applied.
	///
	/// Emits an `ExtrinsicSuccess` or `ExtrinsicFailed` event depending on the outcome.
	/// The emitted event contains the post-dispatch corrected weight including
	/// the base-weight for its dispatch class.
	pub fn note_applied_extrinsic(r: &DispatchResultWithPostInfo, mut info: DispatchInfo) {
		info.weight = extract_actual_weight(r, &info)
			.saturating_add(T::BlockWeights::get().get(info.class).base_extrinsic);
		info.pays_fee = extract_actual_pays_fee(r, &info);

		Self::deposit_event(match r {
			Ok(_) => Event::ExtrinsicSuccess { dispatch_info: info },
			Err(err) => {
				log::trace!(
					target: LOG_TARGET,
					"Extrinsic failed at block({:?}): {:?}",
					Self::block_number(),
					err,
				);
				Event::ExtrinsicFailed { dispatch_error: err.error, dispatch_info: info }
			},
		});

		let next_extrinsic_index = Self::extrinsic_index().unwrap_or_default() + 1u32;

		storage::unhashed::put(well_known_keys::EXTRINSIC_INDEX, &next_extrinsic_index);
		ExecutionPhase::<T>::put(Phase::ApplyExtrinsic(next_extrinsic_index));
	}

	/// To be called immediately after `note_applied_extrinsic` of the last extrinsic of the block
	/// has been called.
	pub fn note_finished_extrinsics() {
		let extrinsic_index: u32 =
			storage::unhashed::take(well_known_keys::EXTRINSIC_INDEX).unwrap_or_default();
		ExtrinsicCount::<T>::put(extrinsic_index);
		ExecutionPhase::<T>::put(Phase::Finalization);
	}

	/// To be called immediately after finishing the initialization of the block
	/// (e.g., called `on_initialize` for all pallets).
	pub fn note_finished_initialize() {
		ExecutionPhase::<T>::put(Phase::ApplyExtrinsic(0))
	}

	/// An account is being created.
	pub fn on_created_account(who: T::AccountId, _a: &mut AccountInfo<T::Index, T::AccountData>) {
		T::OnNewAccount::on_new_account(&who);
		Self::deposit_event(Event::NewAccount { account: who });
	}

	/// Do anything that needs to be done after an account has been killed.
	fn on_killed_account(who: T::AccountId) {
		T::OnKilledAccount::on_killed_account(&who);
		Self::deposit_event(Event::KilledAccount { account: who });
	}

	/// Determine whether or not it is possible to update the code.
	///
	/// Checks the given code if it is a valid runtime wasm blob by instantianting
	/// it and extracting the runtime version of it. It checks that the runtime version
	/// of the old and new runtime has the same spec name and that the spec version is increasing.
	pub fn can_set_code(code: &[u8]) -> Result<(), sp_runtime::DispatchError> {
		let current_version = T::Version::get();
		let new_version = sp_io::misc::runtime_version(code)
			.and_then(|v| RuntimeVersion::decode(&mut &v[..]).ok())
			.ok_or(Error::<T>::FailedToExtractRuntimeVersion)?;

		cfg_if::cfg_if! {
			if #[cfg(all(feature = "runtime-benchmarks", not(test)))] {
					// Let's ensure the compiler doesn't optimize our fetching of the runtime version away.
					core::hint::black_box((new_version, current_version));
					Ok(())
			} else {
				if new_version.spec_name != current_version.spec_name {
					return Err(Error::<T>::InvalidSpecName.into())
				}

				if new_version.spec_version <= current_version.spec_version {
					return Err(Error::<T>::SpecVersionNeedsToIncrease.into())
				}

				Ok(())
			}
		}
	}
}

/// Returns a 32 byte datum which is guaranteed to be universally unique. `entropy` is provided
/// as a facility to reduce the potential for precalculating results.
pub fn unique(entropy: impl Encode) -> [u8; 32] {
	let mut last = [0u8; 32];
	sp_io::storage::read(well_known_keys::INTRABLOCK_ENTROPY, &mut last[..], 0);
	let next = (b"frame_system::unique", entropy, last).using_encoded(blake2_256);
	sp_io::storage::set(well_known_keys::INTRABLOCK_ENTROPY, &next);
	next
}

/// Event handler which registers a provider when created.
pub struct Provider<T>(PhantomData<T>);
impl<T: Config> HandleLifetime<T::AccountId> for Provider<T> {
	fn created(t: &T::AccountId) -> Result<(), DispatchError> {
		Pallet::<T>::inc_providers(t);
		Ok(())
	}
	fn killed(t: &T::AccountId) -> Result<(), DispatchError> {
		Pallet::<T>::dec_providers(t).map(|_| ())
	}
}

/// Event handler which registers a self-sufficient when created.
pub struct SelfSufficient<T>(PhantomData<T>);
impl<T: Config> HandleLifetime<T::AccountId> for SelfSufficient<T> {
	fn created(t: &T::AccountId) -> Result<(), DispatchError> {
		Pallet::<T>::inc_sufficients(t);
		Ok(())
	}
	fn killed(t: &T::AccountId) -> Result<(), DispatchError> {
		Pallet::<T>::dec_sufficients(t);
		Ok(())
	}
}

/// Event handler which registers a consumer when created.
pub struct Consumer<T>(PhantomData<T>);
impl<T: Config> HandleLifetime<T::AccountId> for Consumer<T> {
	fn created(t: &T::AccountId) -> Result<(), DispatchError> {
		Pallet::<T>::inc_consumers(t)
	}
	fn killed(t: &T::AccountId) -> Result<(), DispatchError> {
		Pallet::<T>::dec_consumers(t);
		Ok(())
	}
}

impl<T: Config> BlockNumberProvider for Pallet<T> {
	type BlockNumber = <T as Config>::BlockNumber;

	fn current_block_number() -> Self::BlockNumber {
		Pallet::<T>::block_number()
	}
}

/// Implement StoredMap for a simple single-item, provide-when-not-default system. This works fine
/// for storing a single item which allows the account to continue existing as long as it's not
/// empty/default.
///
/// Anything more complex will need more sophisticated logic.
impl<T: Config> StoredMap<T::AccountId, T::AccountData> for Pallet<T> {
	fn get(k: &T::AccountId) -> T::AccountData {
		Account::<T>::get(k).data
	}

	fn try_mutate_exists<R, E: From<DispatchError>>(
		k: &T::AccountId,
		f: impl FnOnce(&mut Option<T::AccountData>) -> Result<R, E>,
	) -> Result<R, E> {
		let account = Account::<T>::get(k);
		let is_default = account.data == T::AccountData::default();
		let mut some_data = if is_default { None } else { Some(account.data) };
		let result = f(&mut some_data)?;
		if Self::providers(k) > 0 || Self::sufficients(k) > 0 {
			Account::<T>::mutate(k, |a| a.data = some_data.unwrap_or_default());
		} else {
			Account::<T>::remove(k)
		}
		Ok(result)
	}
}

/// Split an `option` into two constituent options, as defined by a `splitter` function.
pub fn split_inner<T, R, S>(
	option: Option<T>,
	splitter: impl FnOnce(T) -> (R, S),
) -> (Option<R>, Option<S>) {
	match option {
		Some(inner) => {
			let (r, s) = splitter(inner);
			(Some(r), Some(s))
		},
		None => (None, None),
	}
}

pub struct ChainContext<T>(PhantomData<T>);
impl<T> Default for ChainContext<T> {
	fn default() -> Self {
		ChainContext(PhantomData)
	}
}

impl<T: Config> Lookup for ChainContext<T> {
	type Source = <T::Lookup as StaticLookup>::Source;
	type Target = <T::Lookup as StaticLookup>::Target;

	fn lookup(&self, s: Self::Source) -> Result<Self::Target, LookupError> {
		<T::Lookup as StaticLookup>::lookup(s)
	}
}

/// Prelude to be used alongside pallet macro, for ease of use.
pub mod pallet_prelude {
	pub use crate::{ensure_none, ensure_root, ensure_signed, ensure_signed_or_root};

	/// Type alias for the `Origin` associated type of system config.
	pub type OriginFor<T> = <T as crate::Config>::RuntimeOrigin;

	/// Type alias for the `BlockNumber` associated type of system config.
	pub type BlockNumberFor<T> = <T as crate::Config>::BlockNumber;
}
