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

//! # Pallet State Trie Migration
//!
//! Reads and writes all keys and values in the entire state in a systematic way. This is useful for
//! upgrading a chain to [`sp-core::StateVersion::V1`], where all keys need to be touched.
//!
//! ## Migration Types
//!
//! This pallet provides 2 ways to do this, each of which is suited for a particular use-case, and
//! can be enabled independently.
//!
//! ### Auto migration
//!
//! This system will try and migrate all keys by continuously using `on_initialize`. It is only
//! sensible for a relay chain or a solo chain, where going slightly over weight is not a problem.
//! It can be configured so that the migration takes at most `n` items and tries to not go over `x`
//! bytes, but the latter is not guaranteed.
//!
//! For example, if a chain contains keys of 1 byte size, the `on_initialize` could read up to `x -
//! 1` bytes from `n` different keys, while the next key is suddenly `:code:`, and there is no way
//! to bail out of this.
//!
//! ### Signed migration
//!
//! As a backup, the migration process can be set in motion via signed transactions that basically
//! say in advance how many items and how many bytes they will consume, and pay for it as well. This
//! can be a good safe alternative, if the former system is not desirable.
//!
//! The (minor) caveat of this approach is that we cannot know in advance how many bytes reading a
//! certain number of keys will incur. To overcome this, the runtime needs to configure this pallet
//! with a `SignedDepositPerItem`. This is the per-item deposit that the origin of the signed
//! migration transactions need to have in their account (on top of the normal fee) and if the size
//! witness data that they claim is incorrect, this deposit is slashed.
//!
//! ---
//!
//! Initially, this pallet does not contain any auto migration. They must be manually enabled by the
//! `ControlOrigin`.

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;
pub mod weights;

const LOG_TARGET: &str = "runtime::state-trie-migration";

#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: crate::LOG_TARGET,
			concat!("[{:?}] 🤖 ", $patter), frame_system::Pallet::<T>::block_number() $(, $values)*
		)
	};
}

#[frame_support::pallet]
pub mod pallet {

	pub use crate::weights::WeightInfo;

	use frame_support::{
		dispatch::{DispatchErrorWithPostInfo, PostDispatchInfo},
		ensure,
		pallet_prelude::*,
		traits::{Currency, Get},
	};
	use frame_system::{self, pallet_prelude::*};
	use sp_core::{
		hexdisplay::HexDisplay, storage::well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX,
	};
	use sp_runtime::{
		self,
		traits::{Saturating, Zero},
	};
	use sp_std::{ops::Deref, prelude::*};

	pub(crate) type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

	/// The progress of either the top or child keys.
	#[derive(
		CloneNoBound,
		Encode,
		Decode,
		scale_info::TypeInfo,
		PartialEqNoBound,
		EqNoBound,
		MaxEncodedLen,
	)]
	#[scale_info(skip_type_params(MaxKeyLen))]
	#[codec(mel_bound())]
	pub enum Progress<MaxKeyLen: Get<u32>> {
		/// Yet to begin.
		ToStart,
		/// Ongoing, with the last key given.
		LastKey(BoundedVec<u8, MaxKeyLen>),
		/// All done.
		Complete,
	}

	/// Convenience type for easier usage of [`Progress`].
	pub type ProgressOf<T> = Progress<<T as Config>::MaxKeyLen>;

	/// A migration task stored in state.
	///
	/// It tracks the last top and child keys read.
	#[derive(Clone, Encode, Decode, scale_info::TypeInfo, PartialEq, Eq, MaxEncodedLen)]
	#[codec(mel_bound(T: Config))]
	#[scale_info(skip_type_params(T))]
	pub struct MigrationTask<T: Config> {
		/// The current top trie migration progress.
		pub(crate) progress_top: ProgressOf<T>,
		/// The current child trie migration progress.
		///
		/// If `ToStart`, no further top keys are processed until the child key migration is
		/// `Complete`.
		pub(crate) progress_child: ProgressOf<T>,

		/// Dynamic counter for the number of items that we have processed in this execution from
		/// the top trie.
		///
		/// It is not written to storage.
		#[codec(skip)]
		pub(crate) dyn_top_items: u32,
		/// Dynamic counter for the number of items that we have processed in this execution from
		/// any child trie.
		///
		/// It is not written to storage.
		#[codec(skip)]
		pub(crate) dyn_child_items: u32,

		/// Dynamic counter for for the byte size of items that we have processed in this
		/// execution.
		///
		/// It is not written to storage.
		#[codec(skip)]
		pub(crate) dyn_size: u32,

		/// The total size of the migration, over all executions.
		///
		/// This only kept around for bookkeeping and debugging.
		pub(crate) size: u32,
		/// The total count of top keys in the migration, over all executions.
		///
		/// This only kept around for bookkeeping and debugging.
		pub(crate) top_items: u32,
		/// The total count of child keys in the migration, over all executions.
		///
		/// This only kept around for bookkeeping and debugging.
		pub(crate) child_items: u32,

		#[codec(skip)]
		pub(crate) _ph: sp_std::marker::PhantomData<T>,
	}

	impl<Size: Get<u32>> sp_std::fmt::Debug for Progress<Size> {
		fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
			match self {
				Progress::ToStart => f.write_str("To start"),
				Progress::LastKey(key) => write!(f, "Last: {:?}", HexDisplay::from(key.deref())),
				Progress::Complete => f.write_str("Complete"),
			}
		}
	}

	impl<T: Config> sp_std::fmt::Debug for MigrationTask<T> {
		fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
			f.debug_struct("MigrationTask")
				.field("top", &self.progress_top)
				.field("child", &self.progress_child)
				.field("dyn_top_items", &self.dyn_top_items)
				.field("dyn_child_items", &self.dyn_child_items)
				.field("dyn_size", &self.dyn_size)
				.field("size", &self.size)
				.field("top_items", &self.top_items)
				.field("child_items", &self.child_items)
				.finish()
		}
	}

	impl<T: Config> Default for MigrationTask<T> {
		fn default() -> Self {
			Self {
				progress_top: Progress::ToStart,
				progress_child: Progress::ToStart,
				dyn_child_items: Default::default(),
				dyn_top_items: Default::default(),
				dyn_size: Default::default(),
				_ph: Default::default(),
				size: Default::default(),
				top_items: Default::default(),
				child_items: Default::default(),
			}
		}
	}

	impl<T: Config> MigrationTask<T> {
		/// Return true if the task is finished.
		pub(crate) fn finished(&self) -> bool {
			matches!(self.progress_top, Progress::Complete)
		}

		/// Check if there's any work left, or if we have exhausted the limits already.
		fn exhausted(&self, limits: MigrationLimits) -> bool {
			self.dyn_total_items() >= limits.item || self.dyn_size >= limits.size
		}

		/// get the total number of keys affected by the current task.
		pub(crate) fn dyn_total_items(&self) -> u32 {
			self.dyn_child_items.saturating_add(self.dyn_top_items)
		}

		/// Migrate keys until either of the given limits are exhausted, or if no more top keys
		/// exist.
		///
		/// Note that this can return after the **first** migration tick that causes exhaustion,
		/// specifically in the case of the `size` constrain. The reason for this is that before
		/// reading a key, we simply cannot know how many bytes it is. In other words, this should
		/// not be used in any environment where resources are strictly bounded (e.g. a parachain),
		/// but it is acceptable otherwise (relay chain, offchain workers).
		pub fn migrate_until_exhaustion(
			&mut self,
			limits: MigrationLimits,
		) -> Result<(), Error<T>> {
			log!(debug, "running migrations on top of {:?} until {:?}", self, limits);

			if limits.item.is_zero() || limits.size.is_zero() {
				// handle this minor edge case, else we would call `migrate_tick` at least once.
				log!(warn, "limits are zero. stopping");
				return Ok(())
			}

			while !self.exhausted(limits) && !self.finished() {
				if let Err(e) = self.migrate_tick() {
					log!(error, "migrate_until_exhaustion failed: {:?}", e);
					return Err(e)
				}
			}

			// accumulate dynamic data into the storage items.
			self.size = self.size.saturating_add(self.dyn_size);
			self.child_items = self.child_items.saturating_add(self.dyn_child_items);
			self.top_items = self.top_items.saturating_add(self.dyn_top_items);
			log!(debug, "finished with {:?}", self);
			Ok(())
		}

		/// Migrate AT MOST ONE KEY. This can be either a top or a child key.
		///
		/// This function is *the* core of this entire pallet.
		fn migrate_tick(&mut self) -> Result<(), Error<T>> {
			match (&self.progress_top, &self.progress_child) {
				(Progress::ToStart, _) => self.migrate_top(),
				(Progress::LastKey(_), Progress::LastKey(_)) => {
					// we're in the middle of doing work on a child tree.
					self.migrate_child()
				},
				(Progress::LastKey(top_key), Progress::ToStart) => {
					// 3. this is the root of a child key, and we are finishing all child-keys (and
					// should call `migrate_top`).

					// NOTE: this block is written intentionally to verbosely for easy of
					// verification.
					if !top_key.starts_with(DEFAULT_CHILD_STORAGE_KEY_PREFIX) {
						// we continue the top key migrations.
						// continue the top key migration
						self.migrate_top()
					} else {
						// this is the root of a child key, and we start processing child keys (and
						// should call `migrate_child`).
						self.migrate_child()
					}
				},
				(Progress::LastKey(_), Progress::Complete) => {
					// we're done with migrating a child-root.
					self.migrate_top()?;
					self.progress_child = Progress::ToStart;
					Ok(())
				},
				(Progress::Complete, _) => {
					// nada
					Ok(())
				},
			}
		}

		/// Migrate the current child key, setting it to its new value, if one exists.
		///
		/// It updates the dynamic counters.
		fn migrate_child(&mut self) -> Result<(), Error<T>> {
			use sp_io::default_child_storage as child_io;
			let (maybe_current_child, child_root) = match (&self.progress_child, &self.progress_top)
			{
				(Progress::LastKey(last_child), Progress::LastKey(last_top)) => {
					let child_root = Pallet::<T>::transform_child_key_or_halt(last_top);
					let maybe_current_child: Option<BoundedVec<u8, T::MaxKeyLen>> =
						if let Some(next) = child_io::next_key(child_root, last_child) {
							Some(next.try_into().map_err(|_| Error::<T>::KeyTooLong)?)
						} else {
							None
						};

					(maybe_current_child, child_root)
				},
				(Progress::ToStart, Progress::LastKey(last_top)) => {
					let child_root = Pallet::<T>::transform_child_key_or_halt(last_top);
					// Start with the empty key as first key.
					(Some(Default::default()), child_root)
				},
				_ => {
					// defensive: there must be an ongoing top migration.
					frame_support::defensive!("cannot migrate child key.");
					return Ok(())
				},
			};

			if let Some(current_child) = maybe_current_child.as_ref() {
				let added_size = if let Some(data) = child_io::get(child_root, current_child) {
					child_io::set(child_root, current_child, &data);
					data.len() as u32
				} else {
					Zero::zero()
				};
				self.dyn_size = self.dyn_size.saturating_add(added_size);
				self.dyn_child_items.saturating_inc();
			}

			log!(trace, "migrated a child key, next_child_key: {:?}", maybe_current_child);
			self.progress_child = match maybe_current_child {
				Some(last_child) => Progress::LastKey(last_child),
				None => Progress::Complete,
			};
			Ok(())
		}

		/// Migrate the current top key, setting it to its new value, if one exists.
		///
		/// It updates the dynamic counters.
		fn migrate_top(&mut self) -> Result<(), Error<T>> {
			let maybe_current_top = match &self.progress_top {
				Progress::LastKey(last_top) => {
					let maybe_top: Option<BoundedVec<u8, T::MaxKeyLen>> =
						if let Some(next) = sp_io::storage::next_key(last_top) {
							Some(next.try_into().map_err(|_| Error::<T>::KeyTooLong)?)
						} else {
							None
						};
					maybe_top
				},
				// Start with the empty key as first key.
				Progress::ToStart => Some(Default::default()),
				Progress::Complete => {
					// defensive: there must be an ongoing top migration.
					frame_support::defensive!("cannot migrate top key.");
					return Ok(())
				},
			};

			if let Some(current_top) = maybe_current_top.as_ref() {
				let added_size = if let Some(data) = sp_io::storage::get(current_top) {
					sp_io::storage::set(current_top, &data);
					data.len() as u32
				} else {
					Zero::zero()
				};
				self.dyn_size = self.dyn_size.saturating_add(added_size);
				self.dyn_top_items.saturating_inc();
			}

			log!(trace, "migrated a top key, next_top_key = {:?}", maybe_current_top);
			self.progress_top = match maybe_current_top {
				Some(last_top) => Progress::LastKey(last_top),
				None => Progress::Complete,
			};
			Ok(())
		}
	}

	/// The limits of a migration.
	#[derive(
		Clone,
		Copy,
		Encode,
		Decode,
		scale_info::TypeInfo,
		Default,
		Debug,
		PartialEq,
		Eq,
		MaxEncodedLen,
	)]
	pub struct MigrationLimits {
		/// The byte size limit.
		pub size: u32,
		/// The number of keys limit.
		pub item: u32,
	}

	/// How a migration was computed.
	#[derive(Clone, Copy, Encode, Decode, scale_info::TypeInfo, Debug, PartialEq, Eq)]
	pub enum MigrationCompute {
		/// A signed origin triggered the migration.
		Signed,
		/// An automatic task triggered the migration.
		Auto,
	}

	/// Inner events of this pallet.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Given number of `(top, child)` keys were migrated respectively, with the given
		/// `compute`.
		Migrated { top: u32, child: u32, compute: MigrationCompute },
		/// Some account got slashed by the given amount.
		Slashed { who: T::AccountId, amount: BalanceOf<T> },
		/// The auto migration task finished.
		AutoMigrationFinished,
		/// Migration got halted due to an error or miss-configuration.
		Halted { error: Error<T> },
	}

	/// The outer Pallet struct.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	/// Configurations of this pallet.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Origin that can control the configurations of this pallet.
		type ControlOrigin: frame_support::traits::EnsureOrigin<Self::RuntimeOrigin>;

		/// Filter on which origin that trigger the manual migrations.
		type SignedFilter: EnsureOrigin<Self::RuntimeOrigin, Success = Self::AccountId>;

		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The currency provider type.
		type Currency: Currency<Self::AccountId>;

		/// Maximal number of bytes that a key can have.
		///
		/// FRAME itself does not limit the key length.
		/// The concrete value must therefore depend on your storage usage.
		/// A [`frame_support::storage::StorageNMap`] for example can have an arbitrary number of
		/// keys which are then hashed and concatenated, resulting in arbitrarily long keys.
		///
		/// Use the *state migration RPC* to retrieve the length of the longest key in your
		/// storage: <https://github.com/paritytech/substrate/issues/11642>
		///
		/// The migration will halt with a `Halted` event if this value is too small.
		/// Since there is no real penalty from over-estimating, it is advised to use a large
		/// value. The default is 512 byte.
		///
		/// Some key lengths for reference:
		/// - [`frame_support::storage::StorageValue`]: 32 byte
		/// - [`frame_support::storage::StorageMap`]: 64 byte
		/// - [`frame_support::storage::StorageDoubleMap`]: 96 byte
		///
		/// For more info see
		/// <https://www.shawntabrizi.com/substrate/querying-substrate-storage-via-rpc/>

		#[pallet::constant]
		type MaxKeyLen: Get<u32>;

		/// The amount of deposit collected per item in advance, for signed migrations.
		///
		/// This should reflect the average storage value size in the worse case.
		type SignedDepositPerItem: Get<BalanceOf<Self>>;

		/// The base value of [`Config::SignedDepositPerItem`].
		///
		/// Final deposit is `items * SignedDepositPerItem + SignedDepositBase`.
		type SignedDepositBase: Get<BalanceOf<Self>>;

		/// The weight information of this pallet.
		type WeightInfo: WeightInfo;
	}

	/// Migration progress.
	///
	/// This stores the snapshot of the last migrated keys. It can be set into motion and move
	/// forward by any of the means provided by this pallet.
	#[pallet::storage]
	#[pallet::getter(fn migration_process)]
	pub type MigrationProcess<T> = StorageValue<_, MigrationTask<T>, ValueQuery>;

	/// The limits that are imposed on automatic migrations.
	///
	/// If set to None, then no automatic migration happens.
	#[pallet::storage]
	#[pallet::getter(fn auto_limits)]
	pub type AutoLimits<T> = StorageValue<_, Option<MigrationLimits>, ValueQuery>;

	/// The maximum limits that the signed migration could use.
	///
	/// If not set, no signed submission is allowed.
	#[pallet::storage]
	#[pallet::getter(fn signed_migration_max_limits)]
	pub type SignedMigrationMaxLimits<T> = StorageValue<_, MigrationLimits, OptionQuery>;

	#[pallet::error]
	#[derive(Clone, PartialEq)]
	pub enum Error<T> {
		/// Max signed limits not respected.
		MaxSignedLimits,
		/// A key was longer than the configured maximum.
		///
		/// This means that the migration halted at the current [`Progress`] and
		/// can be resumed with a larger [`crate::Config::MaxKeyLen`] value.
		/// Retrying with the same [`crate::Config::MaxKeyLen`] value will not work.
		/// The value should only be increased to avoid a storage migration for the currently
		/// stored [`crate::Progress::LastKey`].
		KeyTooLong,
		/// submitter does not have enough funds.
		NotEnoughFunds,
		/// Bad witness data provided.
		BadWitness,
		/// Signed migration is not allowed because the maximum limit is not set yet.
		SignedMigrationNotAllowed,
		/// Bad child root provided.
		BadChildRoot,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Control the automatic migration.
		///
		/// The dispatch origin of this call must be [`Config::ControlOrigin`].
		#[pallet::call_index(0)]
		#[pallet::weight(T::DbWeight::get().reads_writes(1, 1))]
		pub fn control_auto_migration(
			origin: OriginFor<T>,
			maybe_config: Option<MigrationLimits>,
		) -> DispatchResult {
			T::ControlOrigin::ensure_origin(origin)?;
			AutoLimits::<T>::put(maybe_config);
			Ok(())
		}

		/// Continue the migration for the given `limits`.
		///
		/// The dispatch origin of this call can be any signed account.
		///
		/// This transaction has NO MONETARY INCENTIVES. calling it will not reward anyone. Albeit,
		/// Upon successful execution, the transaction fee is returned.
		///
		/// The (potentially over-estimated) of the byte length of all the data read must be
		/// provided for up-front fee-payment and weighing. In essence, the caller is guaranteeing
		/// that executing the current `MigrationTask` with the given `limits` will not exceed
		/// `real_size_upper` bytes of read data.
		///
		/// The `witness_task` is merely a helper to prevent the caller from being slashed or
		/// generally trigger a migration that they do not intend. This parameter is just a message
		/// from caller, saying that they believed `witness_task` was the last state of the
		/// migration, and they only wish for their transaction to do anything, if this assumption
		/// holds. In case `witness_task` does not match, the transaction fails.
		///
		/// Based on the documentation of [`MigrationTask::migrate_until_exhaustion`], the
		/// recommended way of doing this is to pass a `limit` that only bounds `count`, as the
		/// `size` limit can always be overwritten.
		#[pallet::call_index(1)]
		#[pallet::weight(
			// the migration process
			Pallet::<T>::dynamic_weight(limits.item, * real_size_upper)
			// rest of the operations, like deposit etc.
			+ T::WeightInfo::continue_migrate()
		)]
		pub fn continue_migrate(
			origin: OriginFor<T>,
			limits: MigrationLimits,
			real_size_upper: u32,
			witness_task: MigrationTask<T>,
		) -> DispatchResultWithPostInfo {
			let who = T::SignedFilter::ensure_origin(origin)?;

			let max_limits =
				Self::signed_migration_max_limits().ok_or(Error::<T>::SignedMigrationNotAllowed)?;
			ensure!(
				limits.size <= max_limits.size && limits.item <= max_limits.item,
				Error::<T>::MaxSignedLimits,
			);

			// ensure they can pay more than the fee.
			let deposit = T::SignedDepositPerItem::get().saturating_mul(limits.item.into());
			ensure!(T::Currency::can_slash(&who, deposit), Error::<T>::NotEnoughFunds);

			let mut task = Self::migration_process();
			ensure!(
				task == witness_task,
				DispatchErrorWithPostInfo {
					error: Error::<T>::BadWitness.into(),
					post_info: PostDispatchInfo {
						actual_weight: Some(T::WeightInfo::continue_migrate_wrong_witness()),
						pays_fee: Pays::Yes
					}
				}
			);
			let migration = task.migrate_until_exhaustion(limits);

			// ensure that the migration witness data was correct.
			if real_size_upper < task.dyn_size {
				// let the imbalance burn.
				let (_imbalance, _remainder) = T::Currency::slash(&who, deposit);
				Self::deposit_event(Event::<T>::Slashed { who, amount: deposit });
				debug_assert!(_remainder.is_zero());
				return Ok(().into())
			}

			Self::deposit_event(Event::<T>::Migrated {
				top: task.dyn_top_items,
				child: task.dyn_child_items,
				compute: MigrationCompute::Signed,
			});

			// refund and correct the weight.
			let actual_weight = Some(
				Pallet::<T>::dynamic_weight(limits.item, task.dyn_size)
					.saturating_add(T::WeightInfo::continue_migrate()),
			);

			MigrationProcess::<T>::put(task);
			let post_info = PostDispatchInfo { actual_weight, pays_fee: Pays::No };
			if let Err(error) = migration {
				Self::halt(error);
			}
			Ok(post_info)
		}

		/// Migrate the list of top keys by iterating each of them one by one.
		///
		/// This does not affect the global migration process tracker ([`MigrationProcess`]), and
		/// should only be used in case any keys are leftover due to a bug.
		#[pallet::call_index(2)]
		#[pallet::weight(
			T::WeightInfo::migrate_custom_top_success()
				.max(T::WeightInfo::migrate_custom_top_fail())
			.saturating_add(
				Pallet::<T>::dynamic_weight(keys.len() as u32, *witness_size)
			)
		)]
		pub fn migrate_custom_top(
			origin: OriginFor<T>,
			keys: Vec<Vec<u8>>,
			witness_size: u32,
		) -> DispatchResultWithPostInfo {
			let who = T::SignedFilter::ensure_origin(origin)?;

			// ensure they can pay more than the fee.
			let deposit = T::SignedDepositBase::get().saturating_add(
				T::SignedDepositPerItem::get().saturating_mul((keys.len() as u32).into()),
			);
			ensure!(T::Currency::can_slash(&who, deposit), "not enough funds");

			let mut dyn_size = 0u32;
			for key in &keys {
				if let Some(data) = sp_io::storage::get(key) {
					dyn_size = dyn_size.saturating_add(data.len() as u32);
					sp_io::storage::set(key, &data);
				}
			}

			if dyn_size > witness_size {
				let (_imbalance, _remainder) = T::Currency::slash(&who, deposit);
				Self::deposit_event(Event::<T>::Slashed { who, amount: deposit });
				debug_assert!(_remainder.is_zero());
				Ok(().into())
			} else {
				Self::deposit_event(Event::<T>::Migrated {
					top: keys.len() as u32,
					child: 0,
					compute: MigrationCompute::Signed,
				});
				Ok(PostDispatchInfo {
					actual_weight: Some(
						T::WeightInfo::migrate_custom_top_success().saturating_add(
							Pallet::<T>::dynamic_weight(keys.len() as u32, dyn_size),
						),
					),
					pays_fee: Pays::Yes,
				})
			}
		}

		/// Migrate the list of child keys by iterating each of them one by one.
		///
		/// All of the given child keys must be present under one `child_root`.
		///
		/// This does not affect the global migration process tracker ([`MigrationProcess`]), and
		/// should only be used in case any keys are leftover due to a bug.
		#[pallet::call_index(3)]
		#[pallet::weight(
			T::WeightInfo::migrate_custom_child_success()
				.max(T::WeightInfo::migrate_custom_child_fail())
			.saturating_add(
				Pallet::<T>::dynamic_weight(child_keys.len() as u32, *total_size)
			)
		)]
		pub fn migrate_custom_child(
			origin: OriginFor<T>,
			root: Vec<u8>,
			child_keys: Vec<Vec<u8>>,
			total_size: u32,
		) -> DispatchResultWithPostInfo {
			use sp_io::default_child_storage as child_io;
			let who = T::SignedFilter::ensure_origin(origin)?;

			// ensure they can pay more than the fee.
			let deposit = T::SignedDepositBase::get().saturating_add(
				T::SignedDepositPerItem::get().saturating_mul((child_keys.len() as u32).into()),
			);
			sp_std::if_std! {
				println!("+ {:?} / {:?} / {:?}", who, deposit, T::Currency::free_balance(&who));
			}
			ensure!(T::Currency::can_slash(&who, deposit), "not enough funds");

			let mut dyn_size = 0u32;
			let transformed_child_key = Self::transform_child_key(&root).ok_or("bad child key")?;
			for child_key in &child_keys {
				if let Some(data) = child_io::get(transformed_child_key, child_key) {
					dyn_size = dyn_size.saturating_add(data.len() as u32);
					child_io::set(transformed_child_key, child_key, &data);
				}
			}

			if dyn_size != total_size {
				let (_imbalance, _remainder) = T::Currency::slash(&who, deposit);
				debug_assert!(_remainder.is_zero());
				Self::deposit_event(Event::<T>::Slashed { who, amount: deposit });
				Ok(PostDispatchInfo {
					actual_weight: Some(T::WeightInfo::migrate_custom_child_fail()),
					pays_fee: Pays::Yes,
				})
			} else {
				Self::deposit_event(Event::<T>::Migrated {
					top: 0,
					child: child_keys.len() as u32,
					compute: MigrationCompute::Signed,
				});
				Ok(PostDispatchInfo {
					actual_weight: Some(
						T::WeightInfo::migrate_custom_child_success().saturating_add(
							Pallet::<T>::dynamic_weight(child_keys.len() as u32, total_size),
						),
					),
					pays_fee: Pays::Yes,
				})
			}
		}

		/// Set the maximum limit of the signed migration.
		#[pallet::call_index(4)]
		#[pallet::weight(T::DbWeight::get().reads_writes(1, 1))]
		pub fn set_signed_max_limits(
			origin: OriginFor<T>,
			limits: MigrationLimits,
		) -> DispatchResult {
			let _ = T::ControlOrigin::ensure_origin(origin)?;
			SignedMigrationMaxLimits::<T>::put(limits);
			Ok(())
		}

		/// Forcefully set the progress the running migration.
		///
		/// This is only useful in one case: the next key to migrate is too big to be migrated with
		/// a signed account, in a parachain context, and we simply want to skip it. A reasonable
		/// example of this would be `:code:`, which is both very expensive to migrate, and commonly
		/// used, so probably it is already migrated.
		///
		/// In case you mess things up, you can also, in principle, use this to reset the migration
		/// process.
		#[pallet::call_index(5)]
		#[pallet::weight(T::DbWeight::get().reads_writes(1, 1))]
		pub fn force_set_progress(
			origin: OriginFor<T>,
			progress_top: ProgressOf<T>,
			progress_child: ProgressOf<T>,
		) -> DispatchResult {
			let _ = T::ControlOrigin::ensure_origin(origin)?;
			MigrationProcess::<T>::mutate(|task| {
				task.progress_top = progress_top;
				task.progress_child = progress_child;
			});
			Ok(())
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_: BlockNumberFor<T>) -> Weight {
			if let Some(limits) = Self::auto_limits() {
				let mut task = Self::migration_process();
				if let Err(e) = task.migrate_until_exhaustion(limits) {
					Self::halt(e);
				}
				let weight = Self::dynamic_weight(task.dyn_total_items(), task.dyn_size);

				log!(
					info,
					"migrated {} top keys, {} child keys, and a total of {} bytes.",
					task.dyn_top_items,
					task.dyn_child_items,
					task.dyn_size,
				);

				if task.finished() {
					Self::deposit_event(Event::<T>::AutoMigrationFinished);
					AutoLimits::<T>::kill();
				} else {
					Self::deposit_event(Event::<T>::Migrated {
						top: task.dyn_top_items,
						child: task.dyn_child_items,
						compute: MigrationCompute::Auto,
					});
				}

				MigrationProcess::<T>::put(task);

				weight
			} else {
				T::DbWeight::get().reads(1)
			}
		}
	}

	impl<T: Config> Pallet<T> {
		/// The real weight of a migration of the given number of `items` with total `size`.
		fn dynamic_weight(items: u32, size: u32) -> frame_support::pallet_prelude::Weight {
			let items = items as u64;
			<T as frame_system::Config>::DbWeight::get()
				.reads_writes(1, 1)
				.saturating_mul(items)
				// we assume that the read/write per-byte weight is the same for child and top tree.
				.saturating_add(T::WeightInfo::process_top_key(size))
		}

		/// Put a stop to all ongoing migrations and logs an error.
		fn halt(error: Error<T>) {
			log!(error, "migration halted due to: {:?}", error);
			AutoLimits::<T>::kill();
			Self::deposit_event(Event::<T>::Halted { error });
		}

		/// Convert a child root key, aka. "Child-bearing top key" into the proper format.
		fn transform_child_key(root: &Vec<u8>) -> Option<&[u8]> {
			use sp_core::storage::{ChildType, PrefixedStorageKey};
			match ChildType::from_prefixed_key(PrefixedStorageKey::new_ref(root)) {
				Some((ChildType::ParentKeyId, root)) => Some(root),
				_ => None,
			}
		}

		/// Same as [`child_io_key`], and it halts the auto/unsigned migrations if a bad child root
		/// is used.
		///
		/// This should be used when we are sure that `root` is a correct default child root.
		fn transform_child_key_or_halt(root: &Vec<u8>) -> &[u8] {
			let key = Self::transform_child_key(root);
			if key.is_none() {
				Self::halt(Error::<T>::BadChildRoot);
			}
			key.unwrap_or_default()
		}

		/// Convert a child root to be in the default child-tree.
		#[cfg(any(test, feature = "runtime-benchmarks"))]
		pub(crate) fn childify(root: &'static str) -> Vec<u8> {
			let mut string = DEFAULT_CHILD_STORAGE_KEY_PREFIX.to_vec();
			string.extend_from_slice(root.as_ref());
			string
		}
	}
}

#[cfg(feature = "runtime-benchmarks")]
mod benchmarks {
	use super::{pallet::Pallet as StateTrieMigration, *};
	use frame_support::traits::{Currency, Get};
	use sp_runtime::traits::Saturating;
	use sp_std::prelude::*;

	// The size of the key seemingly makes no difference in the read/write time, so we make it
	// constant.
	const KEY: &[u8] = b"key";

	frame_benchmarking::benchmarks! {
		continue_migrate {
			// note that this benchmark should migrate nothing, as we only want the overhead weight
			// of the bookkeeping, and the migration cost itself is noted via the `dynamic_weight`
			// function.
			let null = MigrationLimits::default();
			let caller = frame_benchmarking::whitelisted_caller();
			// Allow signed migrations.
			SignedMigrationMaxLimits::<T>::put(MigrationLimits { size: 1024, item: 5 });
		}: _(frame_system::RawOrigin::Signed(caller), null, 0, StateTrieMigration::<T>::migration_process())
		verify {
			assert_eq!(StateTrieMigration::<T>::migration_process(), Default::default())
		}

		continue_migrate_wrong_witness {
			let null = MigrationLimits::default();
			let caller = frame_benchmarking::whitelisted_caller();
			let bad_witness = MigrationTask { progress_top: Progress::LastKey(vec![1u8].try_into().unwrap()), ..Default::default() };
		}: {
			assert!(
				StateTrieMigration::<T>::continue_migrate(
					frame_system::RawOrigin::Signed(caller).into(),
					null,
					0,
					bad_witness,
				)
				.is_err()
			)
		}
		verify {
			assert_eq!(StateTrieMigration::<T>::migration_process(), Default::default())
		}

		migrate_custom_top_success {
			let null = MigrationLimits::default();
			let caller = frame_benchmarking::whitelisted_caller();
			let deposit = T::SignedDepositBase::get().saturating_add(
				T::SignedDepositPerItem::get().saturating_mul(1u32.into()),
			);
			let stash = T::Currency::minimum_balance() * BalanceOf::<T>::from(1000u32) + deposit;
			T::Currency::make_free_balance_be(&caller, stash);
		}: migrate_custom_top(frame_system::RawOrigin::Signed(caller.clone()), Default::default(), 0)
		verify {
			assert_eq!(StateTrieMigration::<T>::migration_process(), Default::default());
			assert_eq!(T::Currency::free_balance(&caller), stash)
		}

		migrate_custom_top_fail {
			let null = MigrationLimits::default();
			let caller = frame_benchmarking::whitelisted_caller();
			let deposit = T::SignedDepositBase::get().saturating_add(
				T::SignedDepositPerItem::get().saturating_mul(1u32.into()),
			);
			let stash = T::Currency::minimum_balance() * BalanceOf::<T>::from(1000u32) + deposit;
			T::Currency::make_free_balance_be(&caller, stash);
			// for tests, we need to make sure there is _something_ in storage that is being
			// migrated.
			sp_io::storage::set(b"foo", vec![1u8;33].as_ref());
		}: {
			assert!(
				StateTrieMigration::<T>::migrate_custom_top(
					frame_system::RawOrigin::Signed(caller.clone()).into(),
					vec![b"foo".to_vec()],
					1,
				).is_ok()
			);

			frame_system::Pallet::<T>::assert_last_event(
				<T as Config>::RuntimeEvent::from(crate::Event::Slashed {
					who: caller.clone(),
					amount: T::SignedDepositBase::get()
						.saturating_add(T::SignedDepositPerItem::get().saturating_mul(1u32.into())),
				}).into(),
			);
		}
		verify {
			assert_eq!(StateTrieMigration::<T>::migration_process(), Default::default());
			// must have gotten slashed
			assert!(T::Currency::free_balance(&caller) < stash)
		}

		migrate_custom_child_success {
			let caller = frame_benchmarking::whitelisted_caller();
			let deposit = T::SignedDepositBase::get().saturating_add(
				T::SignedDepositPerItem::get().saturating_mul(1u32.into()),
			);
			let stash = T::Currency::minimum_balance() * BalanceOf::<T>::from(1000u32) + deposit;
			T::Currency::make_free_balance_be(&caller, stash);
		}: migrate_custom_child(
			frame_system::RawOrigin::Signed(caller.clone()),
			StateTrieMigration::<T>::childify(Default::default()),
			Default::default(),
			0
		)
		verify {
			assert_eq!(StateTrieMigration::<T>::migration_process(), Default::default());
			assert_eq!(T::Currency::free_balance(&caller), stash);
		}

		migrate_custom_child_fail {
			let caller = frame_benchmarking::whitelisted_caller();
			let deposit = T::SignedDepositBase::get().saturating_add(
				T::SignedDepositPerItem::get().saturating_mul(1u32.into()),
			);
			let stash = T::Currency::minimum_balance() * BalanceOf::<T>::from(1000u32) + deposit;
			T::Currency::make_free_balance_be(&caller, stash);
			// for tests, we need to make sure there is _something_ in storage that is being
			// migrated.
			sp_io::default_child_storage::set(b"top", b"foo", vec![1u8;33].as_ref());
		}: {
			assert!(
				StateTrieMigration::<T>::migrate_custom_child(
					frame_system::RawOrigin::Signed(caller.clone()).into(),
					StateTrieMigration::<T>::childify("top"),
					vec![b"foo".to_vec()],
					1,
				).is_ok()
			)
		}
		verify {
			assert_eq!(StateTrieMigration::<T>::migration_process(), Default::default());
			// must have gotten slashed
			assert!(T::Currency::free_balance(&caller) < stash)
		}

		process_top_key {
			let v in 1 .. (4 * 1024 * 1024);

			let value = sp_std::vec![1u8; v as usize];
			sp_io::storage::set(KEY, &value);
		}: {
			let data = sp_io::storage::get(KEY).unwrap();
			sp_io::storage::set(KEY, &data);
			let _next = sp_io::storage::next_key(KEY);
			assert_eq!(data, value);
		}

		impl_benchmark_test_suite!(
			StateTrieMigration,
			crate::mock::new_test_ext(sp_runtime::StateVersion::V0, true, None, None),
			crate::mock::Test
		);
	}
}

#[cfg(test)]
mod mock {
	use super::*;
	use crate as pallet_state_trie_migration;
	use frame_support::{
		parameter_types,
		traits::{ConstU32, ConstU64, Hooks},
		weights::Weight,
	};
	use frame_system::{EnsureRoot, EnsureSigned};
	use sp_core::{
		storage::{ChildInfo, StateVersion},
		H256,
	};
	use sp_runtime::{
		traits::{BlakeTwo256, Header as _, IdentityLookup},
		BuildStorage, StorageChild,
	};

	type Block = frame_system::mocking::MockBlockU32<Test>;

	// Configure a mock runtime to test the pallet.
	frame_support::construct_runtime!(
		pub enum Test
		{
			System: frame_system::{Pallet, Call, Config<T>, Storage, Event<T>},
			Balances: pallet_balances::{Pallet, Call, Config<T>, Storage, Event<T>},
			StateTrieMigration: pallet_state_trie_migration::{Pallet, Call, Storage, Event<T>},
		}
	);

	parameter_types! {
		pub const SS58Prefix: u8 = 42;
	}

	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type RuntimeOrigin = RuntimeOrigin;
		type RuntimeCall = RuntimeCall;
		type Index = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Block = Block;
		type RuntimeEvent = RuntimeEvent;
		type BlockHashCount = ConstU32<250>;
		type DbWeight = ();
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = SS58Prefix;
		type OnSetCode = ();
		type MaxConsumers = ConstU32<16>;
	}

	parameter_types! {
		pub const SignedDepositPerItem: u64 = 1;
		pub const SignedDepositBase: u64 = 5;
		pub const MigrationMaxKeyLen: u32 = 512;
	}

	impl pallet_balances::Config for Test {
		type Balance = u64;
		type RuntimeEvent = RuntimeEvent;
		type DustRemoval = ();
		type ExistentialDeposit = ConstU64<1>;
		type AccountStore = System;
		type MaxLocks = ();
		type MaxReserves = ();
		type ReserveIdentifier = [u8; 8];
		type WeightInfo = ();
		type FreezeIdentifier = ();
		type MaxFreezes = ();
		type RuntimeHoldReason = ();
		type MaxHolds = ();
	}

	/// Test only Weights for state migration.
	pub struct StateMigrationTestWeight;

	impl WeightInfo for StateMigrationTestWeight {
		fn process_top_key(_: u32) -> Weight {
			Weight::from_parts(1000000, 0)
		}
		fn continue_migrate() -> Weight {
			Weight::from_parts(1000000, 0)
		}
		fn continue_migrate_wrong_witness() -> Weight {
			Weight::from_parts(1000000, 0)
		}
		fn migrate_custom_top_fail() -> Weight {
			Weight::from_parts(1000000, 0)
		}
		fn migrate_custom_top_success() -> Weight {
			Weight::from_parts(1000000, 0)
		}
		fn migrate_custom_child_fail() -> Weight {
			Weight::from_parts(1000000, 0)
		}
		fn migrate_custom_child_success() -> Weight {
			Weight::from_parts(1000000, 0)
		}
	}

	impl pallet_state_trie_migration::Config for Test {
		type RuntimeEvent = RuntimeEvent;
		type ControlOrigin = EnsureRoot<u64>;
		type Currency = Balances;
		type MaxKeyLen = MigrationMaxKeyLen;
		type SignedDepositPerItem = SignedDepositPerItem;
		type SignedDepositBase = SignedDepositBase;
		type SignedFilter = EnsureSigned<Self::AccountId>;
		type WeightInfo = StateMigrationTestWeight;
	}

	pub fn new_test_ext(
		version: StateVersion,
		with_pallets: bool,
		custom_keys: Option<Vec<(Vec<u8>, Vec<u8>)>>,
		custom_child: Option<Vec<(Vec<u8>, Vec<u8>, Vec<u8>)>>,
	) -> sp_io::TestExternalities {
		let minimum_size = sp_core::storage::TRIE_VALUE_NODE_THRESHOLD as usize + 1;
		let mut custom_storage = sp_core::storage::Storage {
			top: vec![
				(b"key1".to_vec(), vec![1u8; minimum_size + 1]), // 6b657931
				(b"key2".to_vec(), vec![1u8; minimum_size + 2]), // 6b657931
				(b"key3".to_vec(), vec![1u8; minimum_size + 3]), // 6b657931
				(b"key4".to_vec(), vec![1u8; minimum_size + 4]), // 6b657931
				(b"key5".to_vec(), vec![1u8; minimum_size + 5]), // 6b657932
				(b"key6".to_vec(), vec![1u8; minimum_size + 6]), // 6b657934
				(b"key7".to_vec(), vec![1u8; minimum_size + 7]), // 6b657934
				(b"key8".to_vec(), vec![1u8; minimum_size + 8]), // 6b657934
				(b"key9".to_vec(), vec![1u8; minimum_size + 9]), // 6b657934
				(b"CODE".to_vec(), vec![1u8; minimum_size + 100]), // 434f4445
			]
			.into_iter()
			.chain(custom_keys.unwrap_or_default())
			.collect(),
			children_default: vec![
				(
					b"chk1".to_vec(), // 63686b31
					StorageChild {
						data: vec![
							(b"key1".to_vec(), vec![1u8; 55]),
							(b"key2".to_vec(), vec![2u8; 66]),
						]
						.into_iter()
						.collect(),
						child_info: ChildInfo::new_default(b"chk1"),
					},
				),
				(
					b"chk2".to_vec(),
					StorageChild {
						data: vec![
							(b"key1".to_vec(), vec![1u8; 54]),
							(b"key2".to_vec(), vec![2u8; 64]),
						]
						.into_iter()
						.collect(),
						child_info: ChildInfo::new_default(b"chk2"),
					},
				),
			]
			.into_iter()
			.chain(
				custom_child
					.unwrap_or_default()
					.into_iter()
					.map(|(r, k, v)| {
						(
							r.clone(),
							StorageChild {
								data: vec![(k, v)].into_iter().collect(),
								child_info: ChildInfo::new_default(&r),
							},
						)
					})
					.collect::<Vec<_>>(),
			)
			.collect(),
		};

		if with_pallets {
			frame_system::GenesisConfig::<Test>::default()
				.assimilate_storage(&mut custom_storage)
				.unwrap();
			pallet_balances::GenesisConfig::<Test> { balances: vec![(1, 1000)] }
				.assimilate_storage(&mut custom_storage)
				.unwrap();
		}

		sp_tracing::try_init_simple();
		(custom_storage, version).into()
	}

	pub(crate) fn run_to_block(n: u32) -> (H256, Weight) {
		let mut root = Default::default();
		let mut weight_sum = Weight::zero();
		log::trace!(target: LOG_TARGET, "running from {:?} to {:?}", System::block_number(), n);
		while System::block_number() < n {
			System::set_block_number(System::block_number() + 1);
			System::on_initialize(System::block_number());

			weight_sum += StateTrieMigration::on_initialize(System::block_number());

			root = *System::finalize().state_root();
			System::on_finalize(System::block_number());
		}
		(root, weight_sum)
	}
}

#[cfg(test)]
mod test {
	use super::{mock::*, *};
	use frame_support::{bounded_vec, dispatch::*};
	use sp_runtime::{traits::Bounded, StateVersion};

	#[test]
	fn fails_if_no_migration() {
		let mut ext = new_test_ext(StateVersion::V0, false, None, None);
		let root1 = ext.execute_with(|| run_to_block(30).0);

		let mut ext2 = new_test_ext(StateVersion::V1, false, None, None);
		let root2 = ext2.execute_with(|| run_to_block(30).0);

		// these two roots should not be the same.
		assert_ne!(root1, root2);
	}

	#[test]
	fn halts_if_top_key_too_long() {
		let bad_key = vec![1u8; MigrationMaxKeyLen::get() as usize + 1];
		let bad_top_keys = vec![(bad_key.clone(), vec![])];

		new_test_ext(StateVersion::V0, true, Some(bad_top_keys), None).execute_with(|| {
			System::set_block_number(1);
			assert_eq!(MigrationProcess::<Test>::get(), Default::default());

			// Allow signed migrations.
			SignedMigrationMaxLimits::<Test>::put(MigrationLimits { size: 1 << 20, item: 50 });

			// fails if the top key is too long.
			frame_support::assert_ok!(StateTrieMigration::continue_migrate(
				RuntimeOrigin::signed(1),
				MigrationLimits { item: 50, size: 1 << 20 },
				Bounded::max_value(),
				MigrationProcess::<Test>::get()
			),);
			// The auto migration halted.
			System::assert_last_event(
				crate::Event::Halted { error: Error::<Test>::KeyTooLong }.into(),
			);
			// Limits are killed.
			assert!(AutoLimits::<Test>::get().is_none());

			// Calling `migrate_until_exhaustion` also fails.
			let mut task = StateTrieMigration::migration_process();
			let result = task.migrate_until_exhaustion(
				StateTrieMigration::signed_migration_max_limits().unwrap(),
			);
			assert!(result.is_err());
		});
	}

	#[test]
	fn halts_if_child_key_too_long() {
		let bad_key = vec![1u8; MigrationMaxKeyLen::get() as usize + 1];
		let bad_child_keys = vec![(bad_key.clone(), vec![], vec![])];

		new_test_ext(StateVersion::V0, true, None, Some(bad_child_keys)).execute_with(|| {
			System::set_block_number(1);
			assert_eq!(MigrationProcess::<Test>::get(), Default::default());

			// Allow signed migrations.
			SignedMigrationMaxLimits::<Test>::put(MigrationLimits { size: 1 << 20, item: 50 });

			// fails if the top key is too long.
			frame_support::assert_ok!(StateTrieMigration::continue_migrate(
				RuntimeOrigin::signed(1),
				MigrationLimits { item: 50, size: 1 << 20 },
				Bounded::max_value(),
				MigrationProcess::<Test>::get()
			));
			// The auto migration halted.
			System::assert_last_event(
				crate::Event::Halted { error: Error::<Test>::KeyTooLong }.into(),
			);
			// Limits are killed.
			assert!(AutoLimits::<Test>::get().is_none());

			// Calling `migrate_until_exhaustion` also fails.
			let mut task = StateTrieMigration::migration_process();
			let result = task.migrate_until_exhaustion(
				StateTrieMigration::signed_migration_max_limits().unwrap(),
			);
			assert!(result.is_err());
		});
	}

	#[test]
	fn detects_value_in_empty_top_key() {
		let limit = MigrationLimits { item: 1, size: 1000 };
		let initial_keys = Some(vec![(vec![], vec![66u8; 77])]);
		let mut ext = new_test_ext(StateVersion::V0, false, initial_keys.clone(), None);

		let root_upgraded = ext.execute_with(|| {
			AutoLimits::<Test>::put(Some(limit));
			let root = run_to_block(30).0;

			// eventually everything is over.
			assert!(StateTrieMigration::migration_process().finished());
			root
		});

		let mut ext2 = new_test_ext(StateVersion::V1, false, initial_keys, None);
		let root = ext2.execute_with(|| {
			AutoLimits::<Test>::put(Some(limit));
			run_to_block(30).0
		});

		assert_eq!(root, root_upgraded);
	}

	#[test]
	fn detects_value_in_first_child_key() {
		let limit = MigrationLimits { item: 1, size: 1000 };
		let initial_child = Some(vec![(b"chk1".to_vec(), vec![], vec![66u8; 77])]);
		let mut ext = new_test_ext(StateVersion::V0, false, None, initial_child.clone());

		let root_upgraded = ext.execute_with(|| {
			AutoLimits::<Test>::put(Some(limit));
			let root = run_to_block(30).0;

			// eventually everything is over.
			assert!(StateTrieMigration::migration_process().finished());
			root
		});

		let mut ext2 = new_test_ext(StateVersion::V1, false, None, initial_child);
		let root = ext2.execute_with(|| {
			AutoLimits::<Test>::put(Some(limit));
			run_to_block(30).0
		});

		assert_eq!(root, root_upgraded);
	}

	#[test]
	fn auto_migrate_works() {
		let run_with_limits = |limit, from, until| {
			let mut ext = new_test_ext(StateVersion::V0, false, None, None);
			let root_upgraded = ext.execute_with(|| {
				assert_eq!(AutoLimits::<Test>::get(), None);
				assert_eq!(MigrationProcess::<Test>::get(), Default::default());

				// nothing happens if we don't set the limits.
				let _ = run_to_block(from);
				assert_eq!(MigrationProcess::<Test>::get(), Default::default());

				// this should allow 1 item per block to be migrated.
				AutoLimits::<Test>::put(Some(limit));

				let root = run_to_block(until).0;

				// eventually everything is over.
				assert!(matches!(
					StateTrieMigration::migration_process(),
					MigrationTask { progress_top: Progress::Complete, .. }
				));
				root
			});

			let mut ext2 = new_test_ext(StateVersion::V1, false, None, None);
			let root = ext2.execute_with(|| {
				// update ex2 to contain the new items
				let _ = run_to_block(from);
				AutoLimits::<Test>::put(Some(limit));
				run_to_block(until).0
			});
			assert_eq!(root, root_upgraded);
		};

		// single item
		run_with_limits(MigrationLimits { item: 1, size: 1000 }, 10, 100);
		// multi-item
		run_with_limits(MigrationLimits { item: 5, size: 1000 }, 10, 100);
		// multi-item, based on size. Note that largest value is 100 bytes.
		run_with_limits(MigrationLimits { item: 1000, size: 128 }, 10, 100);
		// unbounded
		run_with_limits(
			MigrationLimits { item: Bounded::max_value(), size: Bounded::max_value() },
			10,
			100,
		);
	}

	#[test]
	fn signed_migrate_works() {
		new_test_ext(StateVersion::V0, true, None, None).execute_with(|| {
			assert_eq!(MigrationProcess::<Test>::get(), Default::default());

			// Allow signed migrations.
			SignedMigrationMaxLimits::<Test>::put(MigrationLimits { size: 1024, item: 5 });

			// can't submit if limit is too high.
			frame_support::assert_err!(
				StateTrieMigration::continue_migrate(
					RuntimeOrigin::signed(1),
					MigrationLimits { item: 5, size: sp_runtime::traits::Bounded::max_value() },
					Bounded::max_value(),
					MigrationProcess::<Test>::get()
				),
				Error::<Test>::MaxSignedLimits,
			);

			// can't submit if poor.
			frame_support::assert_err!(
				StateTrieMigration::continue_migrate(
					RuntimeOrigin::signed(2),
					MigrationLimits { item: 5, size: 100 },
					100,
					MigrationProcess::<Test>::get()
				),
				Error::<Test>::NotEnoughFunds,
			);

			// can't submit with bad witness.
			frame_support::assert_err_ignore_postinfo!(
				StateTrieMigration::continue_migrate(
					RuntimeOrigin::signed(1),
					MigrationLimits { item: 5, size: 100 },
					100,
					MigrationTask {
						progress_top: Progress::LastKey(bounded_vec![1u8]),
						..Default::default()
					}
				),
				Error::<Test>::BadWitness,
			);

			// migrate all keys in a series of submissions
			while !MigrationProcess::<Test>::get().finished() {
				// first we compute the task to get the accurate consumption.
				let mut task = StateTrieMigration::migration_process();
				let result = task.migrate_until_exhaustion(
					StateTrieMigration::signed_migration_max_limits().unwrap(),
				);
				assert!(result.is_ok());

				frame_support::assert_ok!(StateTrieMigration::continue_migrate(
					RuntimeOrigin::signed(1),
					StateTrieMigration::signed_migration_max_limits().unwrap(),
					task.dyn_size,
					MigrationProcess::<Test>::get()
				));

				// no funds should remain reserved.
				assert_eq!(Balances::reserved_balance(&1), 0);

				// and the task should be updated
				assert!(matches!(
					StateTrieMigration::migration_process(),
					MigrationTask { size: x, .. } if x > 0,
				));
			}
		});
	}

	#[test]
	fn custom_migrate_top_works() {
		let correct_witness = 3 + sp_core::storage::TRIE_VALUE_NODE_THRESHOLD * 3 + 1 + 2 + 3;
		new_test_ext(StateVersion::V0, true, None, None).execute_with(|| {
			frame_support::assert_ok!(StateTrieMigration::migrate_custom_top(
				RuntimeOrigin::signed(1),
				vec![b"key1".to_vec(), b"key2".to_vec(), b"key3".to_vec()],
				correct_witness,
			));

			// no funds should remain reserved.
			assert_eq!(Balances::reserved_balance(&1), 0);
			assert_eq!(Balances::free_balance(&1), 1000);
		});

		new_test_ext(StateVersion::V0, true, None, None).execute_with(|| {
			// works if the witness is an overestimate
			frame_support::assert_ok!(StateTrieMigration::migrate_custom_top(
				RuntimeOrigin::signed(1),
				vec![b"key1".to_vec(), b"key2".to_vec(), b"key3".to_vec()],
				correct_witness + 99,
			));

			// no funds should remain reserved.
			assert_eq!(Balances::reserved_balance(&1), 0);
			assert_eq!(Balances::free_balance(&1), 1000);
		});

		new_test_ext(StateVersion::V0, true, None, None).execute_with(|| {
			assert_eq!(Balances::free_balance(&1), 1000);

			// note that we don't expect this to be a noop -- we do slash.
			frame_support::assert_ok!(StateTrieMigration::migrate_custom_top(
				RuntimeOrigin::signed(1),
				vec![b"key1".to_vec(), b"key2".to_vec(), b"key3".to_vec()],
				correct_witness - 1,
			),);

			// no funds should remain reserved.
			assert_eq!(Balances::reserved_balance(&1), 0);
			assert_eq!(
				Balances::free_balance(&1),
				1000 - (3 * SignedDepositPerItem::get() + SignedDepositBase::get())
			);
		});
	}

	#[test]
	fn custom_migrate_child_works() {
		new_test_ext(StateVersion::V0, true, None, None).execute_with(|| {
			frame_support::assert_ok!(StateTrieMigration::migrate_custom_child(
				RuntimeOrigin::signed(1),
				StateTrieMigration::childify("chk1"),
				vec![b"key1".to_vec(), b"key2".to_vec()],
				55 + 66,
			));

			// no funds should remain reserved.
			assert_eq!(Balances::reserved_balance(&1), 0);
			assert_eq!(Balances::free_balance(&1), 1000);
		});

		new_test_ext(StateVersion::V0, true, None, None).execute_with(|| {
			assert_eq!(Balances::free_balance(&1), 1000);

			// note that we don't expect this to be a noop -- we do slash.
			frame_support::assert_ok!(StateTrieMigration::migrate_custom_child(
				RuntimeOrigin::signed(1),
				StateTrieMigration::childify("chk1"),
				vec![b"key1".to_vec(), b"key2".to_vec()],
				999999, // wrong witness
			));

			// no funds should remain reserved.
			assert_eq!(Balances::reserved_balance(&1), 0);
			assert_eq!(
				Balances::free_balance(&1),
				1000 - (2 * SignedDepositPerItem::get() + SignedDepositBase::get())
			);
		});
	}
}

/// Exported set of tests to be called against different runtimes.
#[cfg(feature = "remote-test")]
pub(crate) mod remote_tests {
	use crate::{AutoLimits, MigrationLimits, Pallet as StateTrieMigration, LOG_TARGET};
	use codec::Encode;
	use frame_support::{
		traits::{Get, Hooks},
		weights::Weight,
	};
	use frame_system::{pallet_prelude::BlockNumberFor, Pallet as System};
	use remote_externalities::Mode;
	use sp_core::H256;
	use sp_runtime::{
		traits::{Block as BlockT, HashFor, Header as _, One, Zero},
		DeserializeOwned,
	};
	use thousands::Separable;

	#[allow(dead_code)]
	fn run_to_block<Runtime: crate::Config<Hash = H256>>(
		n: BlockNumberFor<Runtime>,
	) -> (H256, Weight) {
		let mut root = Default::default();
		let mut weight_sum = Weight::zero();
		while System::<Runtime>::block_number() < n {
			System::<Runtime>::set_block_number(System::<Runtime>::block_number() + One::one());
			System::<Runtime>::on_initialize(System::<Runtime>::block_number());

			weight_sum +=
				StateTrieMigration::<Runtime>::on_initialize(System::<Runtime>::block_number());

			root = System::<Runtime>::finalize().state_root().clone();
			System::<Runtime>::on_finalize(System::<Runtime>::block_number());
		}
		(root, weight_sum)
	}

	/// Run the entire migration, against the given `Runtime`, until completion.
	///
	/// This will print some very useful statistics, make sure [`crate::LOG_TARGET`] is enabled.
	#[allow(dead_code)]
	pub(crate) async fn run_with_limits<Runtime, Block>(limits: MigrationLimits, mode: Mode<Block>)
	where
		Runtime: crate::Config<Hash = H256>,
		Block: BlockT<Hash = H256> + DeserializeOwned,
		Block::Header: serde::de::DeserializeOwned,
	{
		let mut ext = remote_externalities::Builder::<Block>::new()
			.mode(mode)
			.overwrite_state_version(sp_core::storage::StateVersion::V0)
			.build()
			.await
			.unwrap();

		let mut now = ext.execute_with(|| {
			AutoLimits::<Runtime>::put(Some(limits));
			// requires the block number type in our tests to be same as with mainnet, u32.
			frame_system::Pallet::<Runtime>::block_number()
		});

		let mut duration: BlockNumberFor<Runtime> = Zero::zero();
		// set the version to 1, as if the upgrade happened.
		ext.state_version = sp_core::storage::StateVersion::V1;

		let status =
			substrate_state_trie_migration_rpc::migration_status(&ext.as_backend()).unwrap();
		assert!(
			status.top_remaining_to_migrate > 0,
			"no node needs migrating, this probably means that state was initialized with `StateVersion::V1`",
		);

		log::info!(
			target: LOG_TARGET,
			"initial check: top_left: {}, child_left: {}, total_top {}, total_child {}",
			status.top_remaining_to_migrate.separate_with_commas(),
			status.child_remaining_to_migrate.separate_with_commas(),
			status.total_top.separate_with_commas(),
			status.total_child.separate_with_commas(),
		);

		loop {
			let last_state_root = ext.backend.root().clone();
			let ((finished, weight), proof) = ext.execute_and_prove(|| {
				let weight = run_to_block::<Runtime>(now + One::one()).1;
				if StateTrieMigration::<Runtime>::migration_process().finished() {
					return (true, weight)
				}
				duration += One::one();
				now += One::one();
				(false, weight)
			});

			let compact_proof =
				proof.clone().into_compact_proof::<HashFor<Block>>(last_state_root).unwrap();
			log::info!(
				target: LOG_TARGET,
				"proceeded to #{}, weight: [{} / {}], proof: [{} / {} / {}]",
				now,
				weight.separate_with_commas(),
				<Runtime as frame_system::Config>::BlockWeights::get()
					.max_block
					.separate_with_commas(),
				proof.encoded_size().separate_with_commas(),
				compact_proof.encoded_size().separate_with_commas(),
				zstd::stream::encode_all(&compact_proof.encode()[..], 0)
					.unwrap()
					.len()
					.separate_with_commas(),
			);
			ext.commit_all().unwrap();

			if finished {
				break
			}
		}

		ext.execute_with(|| {
			log::info!(
				target: LOG_TARGET,
				"finished on_initialize migration in {} block, final state of the task: {:?}",
				duration,
				StateTrieMigration::<Runtime>::migration_process(),
			)
		});

		let status =
			substrate_state_trie_migration_rpc::migration_status(&ext.as_backend()).unwrap();
		assert_eq!(status.top_remaining_to_migrate, 0);
		assert_eq!(status.child_remaining_to_migrate, 0);
	}
}

#[cfg(all(test, feature = "remote-test"))]
mod remote_tests_local {
	use super::{
		mock::{RuntimeCall as MockCall, *},
		remote_tests::run_with_limits,
		*,
	};
	use remote_externalities::{Mode, OfflineConfig, OnlineConfig, SnapshotConfig};
	use sp_runtime::traits::Bounded;
	use std::env::var as env_var;

	// we only use the hash type from this, so using the mock should be fine.
	type Extrinsic = sp_runtime::testing::TestXt<MockCall, ()>;
	type Block = sp_runtime::testing::Block<Extrinsic>;

	#[tokio::test]
	async fn on_initialize_migration() {
		let snap: SnapshotConfig = env_var("SNAP").expect("Need SNAP env var").into();
		let ws_api = env_var("WS_API").expect("Need WS_API env var").into();

		sp_tracing::try_init_simple();
		let mode = Mode::OfflineOrElseOnline(
			OfflineConfig { state_snapshot: snap.clone() },
			OnlineConfig { transport: ws_api, state_snapshot: Some(snap), ..Default::default() },
		);

		// item being the bottleneck
		run_with_limits::<Test, Block>(
			MigrationLimits { item: 8 * 1024, size: 128 * 1024 * 1024 },
			mode.clone(),
		)
		.await;
		// size being the bottleneck
		run_with_limits::<Test, Block>(
			MigrationLimits { item: Bounded::max_value(), size: 64 * 1024 },
			mode,
		)
		.await;
	}
}
