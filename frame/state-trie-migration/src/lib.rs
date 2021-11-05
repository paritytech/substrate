// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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
//! This pallet provides 3 ways to do this, each of which is suited for a particular use-case, and
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
//! ### Unsigned migration
//!
//! This system will use the offchain worker threads to correct the downside of the previous item:
//! knowing exactly the byte size of migration in each block. Offchain worker threads will first
//! find the maximum number of keys that can be migrated whilst staying below a certain byte size
//! limit offchain, and then submit that back to the chain as an unsigned transaction that can only
//! be included by validators.
//!
//! This approach is safer, and ensures that the migration reads do not take more than a certain
//! amount, yet it does impose some work on the validators/collators.
//!
//! ### Signed migration
//!
//! as a backup, the migration process can be set in motion via signed transactions that basically
//! say in advance how many items and how many bytes they will consume, and pay for it as well. This
//! can be a good safe alternative, if the former two systems are not desirable.
//!
//! The (minor) caveat of this approach is that we cannot know in advance how many bytes reading a
//! certain number of keys will incur. To overcome this, the runtime needs to configure this pallet
//! with a `SignedDepositPerItem`. This is the per-item deposit that the origin of the signed
//! migration transactions need to have in their account (on top of the normal fee) and if the size
//! witness data that they claim is incorrect, this deposit is slashed.
//!
//! ---
//!
//! Initially, this pallet does not contain any auto/unsigned migrations. They must be manually
//! enabled by the `ControlOrigin`. Note that these two migration types cannot co-exist And only one
//! can be enable at each point in time.

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

const LOG_TARGET: &'static str = "runtime::state-trie-migration";

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
	use frame_support::{
		dispatch::TransactionPriority,
		ensure,
		pallet_prelude::*,
		traits::{Currency, Get},
		unsigned::ValidateUnsigned,
	};
	use frame_system::{
		ensure_none, ensure_signed,
		offchain::{SendTransactionTypes, SubmitTransaction},
		pallet_prelude::*,
	};
	use sp_core::{
		hexdisplay::HexDisplay, storage::well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX,
	};
	use sp_runtime::{
		offchain::storage::{MutateStorageError, StorageValueRef},
		traits::{Saturating, Zero},
	};
	use sp_std::prelude::*;

	pub(crate) type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

	/// The weight information of this pallet.
	pub trait WeightInfo {
		fn process_top_key(x: u32) -> Weight;
		fn continue_migrate() -> Weight;
	}

	impl WeightInfo for () {
		fn process_top_key(_: u32) -> Weight {
			1000000
		}
		fn continue_migrate() -> Weight {
			1000000
		}
	}

	/// A migration task stored in state.
	///
	/// It tracks the last top and child keys read.
	#[derive(Clone, Encode, Decode, scale_info::TypeInfo, PartialEq, Eq)]
	#[codec(mel_bound(T: Config))]
	#[scale_info(skip_type_params(T))]
	pub struct MigrationTask<T: Config> {
		/// The top key that we currently have to iterate.
		///
		/// If it does not exist, it means that the migration is done and no further keys exist.
		pub(crate) last_top: Option<Vec<u8>>,
		/// The last child key that we have processed.
		///
		/// This is a child key under the current `self.last_top`.
		///
		/// If this is set, no further top keys are processed until the child key migration is
		/// complete.
		pub(crate) last_child: Option<Vec<u8>>,

		/// A marker to indicate if the previous tick was a child tree migration or not.
		pub(crate) prev_tick_child: bool,

		/// dynamic counter for the number of items that we have processed in this execution from
		/// the top trie.
		///
		/// It is not written to storage.
		#[codec(skip)]
		pub(crate) dyn_top_items: u32,
		/// dynamic counter for the number of items that we have processed in this execution from
		/// any child trie.
		///
		/// It is not written to storage.
		#[codec(skip)]
		pub(crate) dyn_child_items: u32,

		/// dynamic counter for for the byte size of items that we have processed in this
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

	#[cfg(any(feature = "std", feature = "runtime-benchmarks", feature = "try-runtime"))]
	impl<T: Config> sp_std::fmt::Debug for MigrationTask<T> {
		fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
			f.debug_struct("MigrationTask")
				.field(
					"top",
					&self.last_top.as_ref().map(|d| sp_core::hexdisplay::HexDisplay::from(d)),
				)
				.field(
					"child",
					&self.last_child.as_ref().map(|d| sp_core::hexdisplay::HexDisplay::from(d)),
				)
				.field("prev_tick_child", &self.prev_tick_child)
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
				last_top: Some(Default::default()),
				last_child: Default::default(),
				dyn_child_items: Default::default(),
				dyn_top_items: Default::default(),
				dyn_size: Default::default(),
				prev_tick_child: Default::default(),
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
			self.last_top.is_none() && self.last_child.is_none()
		}

		/// Returns `true` if the task fully complies with the given limits.
		pub(crate) fn fully_complies_with(&self, limits: MigrationLimits) -> bool {
			self.dyn_total_items() <= limits.item && self.dyn_size <= limits.size
		}

		/// Check if there's any work left, or if we have exhausted the limits already.
		fn exhausted(&self, limits: MigrationLimits) -> bool {
			self.last_top.is_none() ||
				self.dyn_total_items() >= limits.item ||
				self.dyn_size >= limits.size
		}

		/// get the total number of keys affected by the current task.
		pub(crate) fn dyn_total_items(&self) -> u32 {
			self.dyn_child_items.saturating_add(self.dyn_top_items)
		}

		/// Migrate keys until either of the given limits are exhausted, or if no more top keys
		/// exist.
		///
		/// Note that this returns after the **first** migration tick that causes exhaustion. In
		/// other words, this should not be used in any environment where resources are strictly
		/// bounded (e.g. a parachain), but it is acceptable otherwise (relay chain, offchain
		/// workers).
		pub(crate) fn migrate_until_exhaustion(&mut self, limits: MigrationLimits) {
			log!(debug, "running migrations on top of {:?} until {:?}", self, limits);

			if limits.item.is_zero() || limits.size.is_zero() {
				// handle this minor edge case, else we would call `migrate_tick` at least once.
				log!(warn, "limits are zero. stopping");
				return
			}

			loop {
				self.migrate_tick();
				if self.exhausted(limits) {
					break
				}
			}

			// accumulate dynamic data into the storage items.
			self.size = self.size.saturating_add(self.dyn_size);
			self.child_items = self.child_items.saturating_add(self.dyn_child_items);
			self.top_items = self.top_items.saturating_add(self.dyn_top_items);
			log!(debug, "finished with {:?}", self);
		}

		/// Migrate AT MOST ONE KEY. This can be either a top or a child key.
		///
		/// This function is the core of this entire pallet.
		fn migrate_tick(&mut self) {
			match (self.last_top.as_ref(), self.last_child.as_ref()) {
				(Some(_), Some(_)) => {
					// we're in the middle of doing work on a child tree.
					self.migrate_child();
				},
				(Some(ref top_key), None) => {
					// we have a top key and no child key. 3 possibilities exist:
					// 1. we continue the top key migrations.
					// 2. this is the root of a child key, and we start processing child keys (and
					// should call `migrate_child`).
					// 3. this is the root of a child key, and we are finishing all child-keys (and
					// should call `migrate_top`).

					// NOTE: this block is written intentionally to verbosely for easy of
					// verification.
					match (
						top_key.starts_with(DEFAULT_CHILD_STORAGE_KEY_PREFIX),
						self.prev_tick_child,
					) {
						(false, false) => {
							// continue the top key migration
							self.migrate_top();
						},
						(true, false) => {
							// start going into a child key.
							let maybe_first_child_key = {
								let child_top_key = Pallet::<T>::child_io_key(top_key);
								sp_io::default_child_storage::next_key(child_top_key, &vec![])
							};
							if let Some(first_child_key) = maybe_first_child_key {
								self.last_child = Some(first_child_key);
								self.prev_tick_child = true;
								self.migrate_child();
							} else {
								self.migrate_top();
							}
						},
						(true, true) => {
							// we're done with migrating a child-root.
							self.prev_tick_child = false;
							self.migrate_top();
						},
						(false, true) => {
							// should never happen.
							log!(error, "LOGIC ERROR: unreachable code [0].");
							Pallet::<T>::halt();
						},
					};
				},
				(None, Some(_)) => {
					log!(error, "LOGIC ERROR: unreachable code [1].");
					Pallet::<T>::halt()
				},
				(None, None) => {
					// nada
				},
			}
		}

		/// Migrate the current child key, setting it to its new value, if one exists.
		///
		/// It updates the dynamic counters.
		fn migrate_child(&mut self) {
			let last_child =
				self.last_child.as_ref().expect("value checked to be `Some`; qed");
			let last_top = self.last_top.clone().expect("value checked to be `Some`; qed");

			let child_root = Pallet::<T>::child_io_key(&last_top);
			let added_size = if let Some(data) = sp_io::default_child_storage::get(child_root, &last_child) {
				self.dyn_size = self.dyn_size.saturating_add(data.len() as u32);
				sp_io::default_child_storage::set(child_root, last_child, &data);
				data.len() as u32
			} else {
				Zero::zero()
			};

			self.dyn_child_items.saturating_inc();
			let next_key = sp_io::default_child_storage::next_key(child_root, last_child);
			self.last_child = next_key;
			log!(trace, "migrated a child key with size: {:?}, next task: {:?}", self, added_size);
		}

		/// Migrate the current top key, setting it to its new value, if one exists.
		///
		/// It updates the dynamic counters.
		fn migrate_top(&mut self) {
			let last_top = self.last_top.as_ref().expect("value checked to be `Some`; qed");
			let added_size = if let Some(data) = sp_io::storage::get(&last_top) {
				self.dyn_size = self.dyn_size.saturating_add(data.len() as u32);
				sp_io::storage::set(last_top, &data);
				data.len() as u32
			} else {
				Zero::zero()
			};

			self.dyn_top_items.saturating_inc();
			let next_key = sp_io::storage::next_key(last_top);
			self.last_top = next_key;
			log!(trace, "migrated a top key with size {}, next_task = {:?}", added_size, self);
		}
	}

	/// The limits of a migration.
	#[derive(Clone, Copy, Encode, Decode, scale_info::TypeInfo, Default, Debug, PartialEq, Eq)]
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
		/// An unsigned origin triggered the migration.
		Unsigned,
		/// An automatic task triggered the migration.
		Auto,
	}

	/// Inner events of this pallet.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Given number of `(top, child)` keys were migrated respectively, with the given
		/// `compute`.
		Migrated(u32, u32, MigrationCompute),
	}

	/// The outer Pallet struct.
	#[pallet::pallet]
	#[pallet::generate_store(pub(crate) trait Store)]
	pub struct Pallet<T>(_);

	/// Configurations of this pallet.
	#[pallet::config]
	pub trait Config: frame_system::Config + SendTransactionTypes<Call<Self>> {
		/// Origin that can control the configurations of this pallet.
		type ControlOrigin: frame_support::traits::EnsureOrigin<Self::Origin>;

		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The currency provider type.
		type Currency: Currency<Self::AccountId>;

		/// The amount of deposit collected per item in advance, for signed migrations.
		///
		/// This should reflect the average storage value size in the worse case.
		type SignedDepositPerItem: Get<BalanceOf<Self>>;

		/// The maximum limits that the signed migration could use.
		type SignedMigrationMaxLimits: Get<MigrationLimits>;

		/// The weight information of this pallet.
		type WeightInfo: WeightInfo;

		/// The priority used for unsigned transactions.
		type UnsignedPriority: Get<TransactionPriority>;

		/// The number of items that offchain worker will subtract from the first item count that
		/// causes an over-consumption.
		///
		/// A value around 5-10 is reasonable.
		type UnsignedBackOff: Get<u32>;

		/// The repeat frequency of offchain workers.
		type OffchainRepeat: Get<Self::BlockNumber>;
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

	/// The size limits imposed on unsigned migrations.
	///
	/// This should:
	/// 1. be large enough to accommodate things like `:code`
	/// 2. small enough to never brick a parachain due to PoV limits.
	///
	/// if set to `None`, then no unsigned migration happens.
	#[pallet::storage]
	#[pallet::getter(fn unsigned_limits)]
	pub type UnsignedLimits<T> = StorageValue<_, Option<MigrationLimits>, ValueQuery>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// control the automatic migration.
		///
		/// The dispatch origin of this call must be [`Config::ControlOrigin`].
		#[pallet::weight(T::DbWeight::get().reads_writes(1, 1))]
		pub fn control_auto_migration(
			origin: OriginFor<T>,
			maybe_config: Option<MigrationLimits>,
		) -> DispatchResultWithPostInfo {
			T::ControlOrigin::ensure_origin(origin)?;
			ensure!(
				maybe_config.is_some() ^ Self::unsigned_limits().is_some(),
				"unsigned and auto migration cannot co-exist"
			);
			AutoLimits::<T>::put(maybe_config);
			Ok(().into())
		}

		/// control the unsigned migration.
		///
		/// The dispatch origin of this call must be [`Config::ControlOrigin`].
		#[pallet::weight(T::DbWeight::get().reads_writes(1, 1))]
		pub fn control_unsigned_migration(
			origin: OriginFor<T>,
			maybe_limit: Option<MigrationLimits>,
		) -> DispatchResultWithPostInfo {
			T::ControlOrigin::ensure_origin(origin)?;
			ensure!(
				maybe_limit.is_some() ^ Self::auto_limits().is_some(),
				"unsigned and auto migration cannot co-exist"
			);
			UnsignedLimits::<T>::put(maybe_limit);
			Ok(().into())
		}

		/// The unsigned call that can be submitted by offchain workers.
		///
		/// This can only be valid if it is generated from the local node, which means only
		/// validators can generate this call.
		///
		/// The `item_limit` is the maximum number of items that can be read whilst ensuring that
		/// the migration does not go over `Self::unsigned_limits().size`.
		///
		/// The `witness_size` should always be equal to `Self::unsigned_limits().size` and is only
		/// used for weighing.
		#[pallet::weight(Pallet::<T>::dynamic_weight(*item_limit, *witness_size))]
		pub fn continue_migrate_unsigned(
			origin: OriginFor<T>,
			item_limit: u32,
			witness_size: u32,
			_witness_task: MigrationTask<T>,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;
			let chain_limits =
				Self::unsigned_limits().ok_or("unsigned limit not set, tx not allowed.")?;
			ensure!(witness_size == chain_limits.size, "wrong witness data");

			let mut task = Self::migration_process();
			// pre-dispatch and validate-unsigned already assure this.
			debug_assert_eq!(task, _witness_task);

			// we run the task with the given item limit, and the chain size limit..
			task.migrate_until_exhaustion(MigrationLimits {
				size: chain_limits.size,
				item: item_limit,
			});

			// .. and we assert that the size limit must have been fully met with the given item
			// limit.
			assert!(task.fully_complies_with(chain_limits));

			Self::deposit_event(Event::<T>::Migrated(
				task.dyn_top_items,
				task.dyn_child_items,
				MigrationCompute::Unsigned,
			));
			MigrationProcess::<T>::put(task);

			Ok(().into())
		}

		/// Continue the migration for the given `limits`.
		///
		/// The dispatch origin of this call can be any signed account.
		///
		/// This transaction has NO MONETARY INCENTIVES. calling it will only incur transaction fees
		/// on the caller, with no rewards paid out.
		///
		/// The sum of the byte length of all the data read must be provided for up-front
		/// fee-payment and weighing.
		#[pallet::weight(
			// the migration process
			Pallet::<T>::dynamic_weight(limits.item, * real_size)
			// rest of the operations, like deposit etc.
			+ T::WeightInfo::continue_migrate()
		)]
		pub fn continue_migrate(
			origin: OriginFor<T>,
			limits: MigrationLimits,
			real_size: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			let max_limits = T::SignedMigrationMaxLimits::get();
			ensure!(
				limits.size <= max_limits.size && limits.item <= max_limits.item,
				"max signed limits not respected"
			);

			// ensure they can pay more than the fee.
			let deposit = T::SignedDepositPerItem::get().saturating_mul(limits.item.into());
			ensure!(T::Currency::can_slash(&who, deposit), "not enough funds");

			let mut task = Self::migration_process();
			task.migrate_until_exhaustion(limits);

			// ensure that the migration witness data was correct.
			if real_size != task.dyn_size {
				// let the imbalance burn.
				let (_imbalance, _remainder) = T::Currency::slash(&who, deposit);
				debug_assert!(_remainder.is_zero());
				return Err("Wrong witness data".into())
			}

			Self::deposit_event(Event::<T>::Migrated(
				task.dyn_top_items,
				task.dyn_child_items,
				MigrationCompute::Signed,
			));

			MigrationProcess::<T>::put(task);
			Ok(Pays::No.into())
		}

		/// Migrate the list of top keys by iterating each of them one by one.
		///
		/// This does not affect the global migration process tracker ([`MigrationProcess`]), and
		/// should only be used in case any keys are leftover due to a bug.
		#[pallet::weight(Pallet::<T>::dynamic_weight(keys.len() as u32, *total_size))]
		pub fn migrate_custom_top(
			origin: OriginFor<T>,
			keys: Vec<Vec<u8>>,
			total_size: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// ensure they can pay more than the fee.
			let deposit = T::SignedDepositPerItem::get().saturating_mul((keys.len() as u32).into());
			ensure!(T::Currency::can_slash(&who, deposit), "not enough funds");

			let mut dyn_size = 0u32;
			for key in &keys {
				if let Some(data) = sp_io::storage::get(&key) {
					dyn_size = dyn_size.saturating_add(data.len() as u32);
					sp_io::storage::set(key, &data);
				}
			}

			if dyn_size != total_size {
				let (_imbalance, _remainder) = T::Currency::slash(&who, deposit);
				debug_assert!(_remainder.is_zero());
				return Err("Wrong witness data".into())
			}

			Self::deposit_event(Event::<T>::Migrated(
				keys.len() as u32,
				0,
				MigrationCompute::Signed,
			));
			Ok(().into())
		}

		/// Migrate the list of child keys by iterating each of them one by one.
		///
		/// All of the given child keys must be present under one `top_key`.
		///
		/// This does not affect the global migration process tracker ([`MigrationProcess`]), and
		/// should only be used in case any keys are leftover due to a bug.
		#[pallet::weight(Pallet::<T>::dynamic_weight(child_keys.len() as u32, *total_size))]
		pub fn migrate_custom_child(
			origin: OriginFor<T>,
			top_key: Vec<u8>,
			child_keys: Vec<Vec<u8>>,
			total_size: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// ensure they can pay more than the fee.
			let deposit =
				T::SignedDepositPerItem::get().saturating_mul((child_keys.len() as u32).into());
			ensure!(T::Currency::can_slash(&who, deposit), "not enough funds");

			let mut dyn_size = 0u32;
			for child_key in &child_keys {
				if let Some(data) =
					sp_io::default_child_storage::get(Self::child_io_key(&top_key), &child_key)
				{
					dyn_size = dyn_size.saturating_add(data.len() as u32);
					sp_io::default_child_storage::set(
						Self::child_io_key(&top_key),
						&child_key,
						&data,
					);
				}
			}

			if dyn_size != total_size {
				let (_imbalance, _remainder) = T::Currency::slash(&who, deposit);
				debug_assert!(_remainder.is_zero());
				return Err("Wrong witness data".into())
			}

			Self::deposit_event(Event::<T>::Migrated(
				0,
				child_keys.len() as u32,
				MigrationCompute::Signed,
			));
			Ok(().into())
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn integrity_test() {
			assert!(!T::UnsignedBackOff::get().is_zero(), "UnsignedBackOff should not be zero");
		}

		fn on_initialize(_: BlockNumberFor<T>) -> Weight {
			if let Some(limits) = Self::auto_limits() {
				let mut task = Self::migration_process();
				task.migrate_until_exhaustion(limits);
				let weight = Self::dynamic_weight(task.dyn_total_items(), task.dyn_size);

				log!(
					info,
					"migrated {} top keys, {} child keys, and a total of {} bytes.",
					task.dyn_top_items,
					task.dyn_child_items,
					task.dyn_size,
				);
				Self::deposit_event(Event::<T>::Migrated(
					task.dyn_top_items as u32,
					task.dyn_child_items as u32,
					MigrationCompute::Auto,
				));
				MigrationProcess::<T>::put(task);

				weight
			} else {
				T::DbWeight::get().reads(1)
			}
		}

		fn offchain_worker(now: BlockNumberFor<T>) {
			if Self::ensure_offchain_repeat_frequency(now).is_err() {
				return
			}

			log!(debug, "started offchain worker thread.");
			if let Some(chain_limits) = Self::unsigned_limits() {
				let mut task = Self::migration_process();
				if task.finished() {
					log!(warn, "task is finished, remove `unsigned_limits`.");
					return
				}

				task.migrate_until_exhaustion(chain_limits);

				if task.dyn_size > chain_limits.size {
					// previous `migrate_until_exhaustion` finished with too much size consumption.
					// This most likely means that if it migrated `x` items, now we need to migrate
					// `x - 1` items. But, we migrate less by 5 by default, since the state may have
					// changed between the execution of this offchain worker and time that the
					// transaction reaches the chain.
					log!(
						debug,
						"reducing item count of {} by {}.",
						task.dyn_total_items(),
						T::UnsignedBackOff::get(),
					);
					let mut new_task = Self::migration_process();
					new_task.migrate_until_exhaustion(MigrationLimits {
						size: chain_limits.size,
						item: task.dyn_total_items().saturating_sub(T::UnsignedBackOff::get().max(1)),
					});
					task = new_task;
				}

				let item_limit = task.dyn_total_items();
				if item_limit.is_zero() {
					log!(warn, "can't fit anything in a migration.");
					return
				}

				// with the above if-statement, the limits must now be STRICTLY respected, so we
				// panic and crash the OCW otherwise.
				assert!(
					task.fully_complies_with(chain_limits),
					"runtime::state-trie-migration: The offchain worker failed to create transaction."
				);

				let original_task = Self::migration_process();

				let call = Call::continue_migrate_unsigned {
					item_limit,
					witness_size: chain_limits.size,
					witness_task: original_task,
				};

				match SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into()) {
					Ok(_) => {
						log!(info, "submitted a call to migrate {} items.", item_limit)
					},
					Err(why) => {
						log!(warn, "failed to submit a call to the pool {:?}", why)
					},
				}
			}
		}
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;
		fn validate_unsigned(source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			if let Call::continue_migrate_unsigned { witness_task, .. } = call {
				match source {
					TransactionSource::Local | TransactionSource::InBlock => { /* allowed */ },
					_ => return InvalidTransaction::Call.into(),
				}

				let onchain_task = Self::migration_process();
				if &onchain_task != witness_task {
					return Err(TransactionValidityError::Invalid(InvalidTransaction::Stale))
				}

				ValidTransaction::with_tag_prefix("StorageVersionMigration")
					.priority(T::UnsignedPriority::get())
					// deduplicate based on task data.
					.and_provides(witness_task)
					.longevity(5)
					.propagate(false)
					.build()
			} else {
				InvalidTransaction::Call.into()
			}
		}

		fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
			if let Call::continue_migrate_unsigned { witness_task, .. } = call {
				let onchain_task = Self::migration_process();
				if &onchain_task != witness_task {
					return Err(TransactionValidityError::Invalid(InvalidTransaction::Stale))
				}
				Ok(())
			} else {
				Err(InvalidTransaction::Call.into())
			}
		}
	}

	impl<T: Config> Pallet<T> {
		/// The path used to identify the offchain worker persistent storage.
		const OFFCHAIN_LAST_BLOCK: &'static [u8] = b"parity/state-migration/last-block";

		/// The real weight of a migration of the given number of `items` with total `size`.
		fn dynamic_weight(items: u32, size: u32) -> frame_support::pallet_prelude::Weight {
			let items = items as Weight;
			items
				.saturating_mul(<T as frame_system::Config>::DbWeight::get().reads_writes(1, 1))
				// we assume that the read/write per-byte weight is the same for child and top tree.
				.saturating_add(T::WeightInfo::process_top_key(size))
		}

		/// Put a stop to all ongoing migrations.
		fn halt() {
			UnsignedLimits::<T>::kill();
			AutoLimits::<T>::kill();
		}

		/// Convert a child root key, aka. "Child-bearing top key" into the proper format.
		fn child_io_key(root: &Vec<u8>) -> &[u8] {
			use sp_core::storage::{ChildType, PrefixedStorageKey};
			match ChildType::from_prefixed_key(PrefixedStorageKey::new_ref(root)) {
				Some((ChildType::ParentKeyId, root)) => root,
				None => {
					log!(
						warn,
						"some data seems to be stored under key {:?}, which is a non-default \
						child-trie. This is a logical error and shall not happen.",
						HexDisplay::from(root),
					);
					Self::halt();
					Default::default()
				},
			}
		}

		/// Checks if an execution of the offchain worker is permitted at the given block number, or
		/// not.
		///
		/// This makes sure that
		/// 1. we don't run on previous blocks in case of a re-org
		/// 2. we don't run twice within a window of length `T::OffchainRepeat`.
		///
		/// Returns `Ok(())` if offchain worker limit is respected, `Err(reason)` otherwise. If
		/// `Ok()` is returned, `now` is written in storage and will be used in further calls as the
		/// baseline.
		pub fn ensure_offchain_repeat_frequency(now: T::BlockNumber) -> Result<(), &'static str> {
			let threshold = T::OffchainRepeat::get();
			let last_block = StorageValueRef::persistent(&Self::OFFCHAIN_LAST_BLOCK);

			let mutate_stat = last_block.mutate::<_, &'static str, _>(
				|maybe_head: Result<Option<T::BlockNumber>, _>| {
					match maybe_head {
						Ok(Some(head)) if now < head => Err("fork."),
						Ok(Some(head)) if now >= head && now <= head + threshold =>
							Err("recently executed."),
						Ok(Some(head)) if now > head + threshold => {
							// we can run again now. Write the new head.
							Ok(now)
						},
						_ => {
							// value doesn't exists. Probably this node just booted up. Write, and
							// okay.
							Ok(now)
						},
					}
				},
			);

			match mutate_stat {
				Ok(_) => Ok(()),
				Err(MutateStorageError::ConcurrentModification(_)) =>
					Err("failed to write to offchain db (ConcurrentModification)."),
				Err(MutateStorageError::ValueFunctionFailed(_)) =>
					Err("failed to write to offchain db (ValueFunctionFailed)."),
			}
		}
	}
}

#[cfg(feature = "runtime-benchmarks")]
mod benchmarks {
	use super::*;

	// The size of the key seemingly makes no difference in the read/write time, so we make it
	// constant.
	const KEY: &'static [u8] = b"key";

	frame_benchmarking::benchmarks! {
		continue_migrate {
			let null = MigrationLimits::default();
			let caller = frame_benchmarking::whitelisted_caller();
		}: _(frame_system::RawOrigin::Signed(caller), null, 0)
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
	}
}

#[cfg(test)]
mod mock {
	use parking_lot::RwLock;
	use std::sync::Arc;

	use super::*;
	use crate as pallet_state_trie_migration;
	use frame_support::{parameter_types, traits::Hooks};
	use frame_system::EnsureRoot;
	use sp_core::H256;
	use sp_runtime::{
		offchain::{
			testing::{PoolState, TestOffchainExt, TestTransactionPoolExt},
			OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
		},
		traits::{BlakeTwo256, Dispatchable, Header as _, IdentityLookup},
		StateVersion,
	};

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	// Configure a mock runtime to test the pallet.
	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
			Balances: pallet_balances::{Pallet, Call, Config<T>, Storage, Event<T>},
			StateTrieMigration: pallet_state_trie_migration::{Pallet, Call, Storage, Event<T>},
		}
	);

	parameter_types! {
		pub const BlockHashCount: u32 = 250;
		pub const SS58Prefix: u8 = 42;
	}

	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type Origin = Origin;
		type Call = Call;
		type Index = u64;
		type BlockNumber = u32;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = sp_runtime::generic::Header<Self::BlockNumber, BlakeTwo256>;
		type Event = Event;
		type BlockHashCount = BlockHashCount;
		type DbWeight = ();
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = SS58Prefix;
		type OnSetCode = ();
	}

	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
		pub const OffchainRepeat: u32 = 1;
		pub const SignedDepositPerItem: u64 = 1;
		pub const SignedMigrationMaxLimits: MigrationLimits = MigrationLimits { size: 1024, item: 5 };
	}

	impl pallet_balances::Config for Test {
		type Balance = u64;
		type Event = Event;
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
		type MaxLocks = ();
		type MaxReserves = ();
		type ReserveIdentifier = [u8; 8];
		type WeightInfo = ();
	}

	impl pallet_state_trie_migration::Config for Test {
		type Event = Event;
		type ControlOrigin = EnsureRoot<u64>;
		type Currency = Balances;
		type SignedDepositPerItem = SignedDepositPerItem;
		type SignedMigrationMaxLimits = SignedMigrationMaxLimits;
		type WeightInfo = ();
		type UnsignedPriority = ();
		type UnsignedBackOff = frame_support::traits::ConstU32<2>;
		type OffchainRepeat = OffchainRepeat;
	}

	impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Test
	where
		Call: From<LocalCall>,
	{
		type OverarchingCall = Call;
		type Extrinsic = Extrinsic;
	}

	pub type Extrinsic = sp_runtime::testing::TestXt<Call, ()>;

	pub fn new_test_ext(version: StateVersion, with_pallets: bool) -> sp_io::TestExternalities {
		use sp_core::storage::ChildInfo;

		let mut custom_storage = sp_core::storage::Storage {
			top: vec![
				(b"key1".to_vec(), vec![1u8; 10]),  // 6b657931
				(b"key2".to_vec(), vec![1u8; 20]),  // 6b657931
				(b"key3".to_vec(), vec![1u8; 30]),  // 6b657931
				(b"key4".to_vec(), vec![1u8; 40]),  // 6b657931
				(b"key5".to_vec(), vec![2u8; 50]),  // 6b657932
				(b"key6".to_vec(), vec![3u8; 50]),  // 6b657934
				(b"key7".to_vec(), vec![4u8; 50]),  // 6b657934
				(b"key8".to_vec(), vec![4u8; 50]),  // 6b657934
				(b"key9".to_vec(), vec![4u8; 50]),  // 6b657934
				(b"CODE".to_vec(), vec![1u8; 100]), // 434f4445
			]
			.into_iter()
			.collect(),
			children_default: vec![
				(
					b"chk1".to_vec(), // 63686b31
					sp_core::storage::StorageChild {
						data: vec![
							(b"key1".to_vec(), vec![1u8; 10]),
							(b"key2".to_vec(), vec![2u8; 20]),
						]
						.into_iter()
						.collect(),
						child_info: ChildInfo::new_default(b"chk1"),
					},
				),
				(
					b"chk2".to_vec(),
					sp_core::storage::StorageChild {
						data: vec![
							(b"key1".to_vec(), vec![1u8; 10]),
							(b"key2".to_vec(), vec![2u8; 20]),
						]
						.into_iter()
						.collect(),
						child_info: ChildInfo::new_default(b"chk2"),
					},
				),
			]
			.into_iter()
			.collect(),
		};

		if with_pallets {
			frame_system::GenesisConfig::default()
				.assimilate_storage::<Test>(&mut custom_storage)
				.unwrap();
			pallet_balances::GenesisConfig::<Test> { balances: vec![(1, 1000)] }
				.assimilate_storage(&mut custom_storage)
				.unwrap();
		}

		sp_tracing::try_init_simple();
		(custom_storage, version).into()
	}

	pub fn new_offchain_ext(
		version: StateVersion,
		with_pallets: bool,
	) -> (sp_io::TestExternalities, Arc<RwLock<PoolState>>) {
		let mut ext = new_test_ext(version, with_pallets);
		let pool_state = offchainify(&mut ext);
		(ext, pool_state)
	}

	pub fn offchainify(ext: &mut sp_io::TestExternalities) -> Arc<RwLock<PoolState>> {
		let (offchain, _offchain_state) = TestOffchainExt::new();
		let (pool, pool_state) = TestTransactionPoolExt::new();

		ext.register_extension(OffchainDbExt::new(offchain.clone()));
		ext.register_extension(OffchainWorkerExt::new(offchain));
		ext.register_extension(TransactionPoolExt::new(pool));

		pool_state
	}

	pub fn run_to_block(n: u32) -> H256 {
		let mut root = Default::default();
		while System::block_number() < n {
			System::set_block_number(System::block_number() + 1);
			System::on_initialize(System::block_number());

			StateTrieMigration::on_initialize(System::block_number());

			root = System::finalize().state_root().clone();
			System::on_finalize(System::block_number());
		}
		root
	}

	pub fn run_to_block_and_drain_pool(n: u32, pool: Arc<RwLock<PoolState>>) -> H256 {
		let mut root = Default::default();
		while System::block_number() < n {
			System::set_block_number(System::block_number() + 1);
			System::on_initialize(System::block_number());

			StateTrieMigration::on_initialize(System::block_number());

			// drain previous transactions
			pool.read()
				.transactions
				.clone()
				.into_iter()
				.map(|uxt| <Extrinsic as codec::Decode>::decode(&mut &*uxt).unwrap())
				.for_each(|xt| {
					// dispatch them all with no origin.
					xt.call.dispatch(frame_system::RawOrigin::None.into()).unwrap();
				});
			pool.try_write().unwrap().transactions.clear();

			StateTrieMigration::offchain_worker(System::block_number());

			root = System::finalize().state_root().clone();
			System::on_finalize(System::block_number());
		}
		root
	}
}

#[cfg(test)]
mod test {
	use super::{mock::*, *};
	use sp_runtime::{traits::Bounded, StateVersion};
	use std::sync::Arc;

	#[test]
	fn auto_migrate_works() {
		let run_with_limits = |limit, from, until| {
			let mut ext = new_test_ext(StateVersion::V0, false);
			let root_upgraded = ext.execute_with(|| {
				assert_eq!(AutoLimits::<Test>::get(), None);
				assert_eq!(MigrationProcess::<Test>::get(), Default::default());

				// nothing happens if we don't set the limits.
				let _ = run_to_block(from);
				assert_eq!(MigrationProcess::<Test>::get(), Default::default());

				// this should allow 1 item per block to be migrated.
				AutoLimits::<Test>::put(Some(limit));

				let root = run_to_block(until);

				// eventually everything is over.
				assert!(matches!(
					StateTrieMigration::migration_process(),
					MigrationTask { last_child: None, last_top: None, .. }
				));
				root
			});

			let mut ext2 = new_test_ext(StateVersion::V1, false);
			let root = ext2.execute_with(|| {
				// update ex2 to contain the new items
				let _ = run_to_block(from);
				AutoLimits::<Test>::put(Some(limit));
				run_to_block(until)
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
	fn ocw_migration_works() {
		let run_with_limits = |limits, from, until| {
			let (mut ext, pool) = new_offchain_ext(StateVersion::V0, false);
			let root_upgraded = ext.execute_with(|| {
				assert_eq!(UnsignedLimits::<Test>::get(), None);
				assert_eq!(MigrationProcess::<Test>::get(), Default::default());

				// nothing happens if we don't set the limits.
				run_to_block_and_drain_pool(from, Arc::clone(&pool));
				assert_eq!(MigrationProcess::<Test>::get(), Default::default());

				// allow 2 items per run
				UnsignedLimits::<Test>::put(Some(limits));

				run_to_block_and_drain_pool(until, Arc::clone(&pool))
			});

			let (mut ext2, pool2) = new_offchain_ext(StateVersion::V1, false);
			let root = ext2.execute_with(|| {
				// update ex2 to contain the new items
				run_to_block_and_drain_pool(from, Arc::clone(&pool2));
				UnsignedLimits::<Test>::put(Some(limits));
				run_to_block_and_drain_pool(until, Arc::clone(&pool2))
			});
			assert_eq!(root, root_upgraded);
		};

		// single item
		run_with_limits(MigrationLimits { item: 1, size: 1000 }, 10, 100);
		// multi-item
		run_with_limits(MigrationLimits { item: 5, size: 1000 }, 10, 100);
		// multi-item, based on size
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
		new_test_ext(StateVersion::V0, true).execute_with(|| {
			assert_eq!(MigrationProcess::<Test>::get(), Default::default());

			// can't submit if limit is too high.
			frame_support::assert_err!(
				StateTrieMigration::continue_migrate(
					Origin::signed(1),
					MigrationLimits { item: 5, size: sp_runtime::traits::Bounded::max_value() },
					Bounded::max_value(),
				),
				"max signed limits not respected"
			);

			// can't submit if poor.
			frame_support::assert_err!(
				StateTrieMigration::continue_migrate(
					Origin::signed(2),
					MigrationLimits { item: 5, size: 100 },
					100,
				),
				"not enough funds"
			);

			// migrate all keys in a series of submissions
			while !MigrationProcess::<Test>::get().finished() {
				// first we compute the task to get the accurate consumption.
				let mut task = StateTrieMigration::migration_process();
				task.migrate_until_exhaustion(SignedMigrationMaxLimits::get());

				frame_support::assert_ok!(StateTrieMigration::continue_migrate(
					Origin::signed(1),
					SignedMigrationMaxLimits::get(),
					task.dyn_size
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
	fn custom_migrate_works() {
		new_test_ext(StateVersion::V0, true).execute_with(|| {
			frame_support::assert_ok!(StateTrieMigration::migrate_custom_top(
				Origin::signed(1),
				vec![b"key1".to_vec(), b"key2".to_vec(), b"key3".to_vec()],
				10 + 20 + 30,
			));

			// no funds should remain reserved.
			assert_eq!(Balances::reserved_balance(&1), 0);
		});
	}
}

#[cfg(all(test, feature = "remote-tests"))]
mod remote_tests {
	use std::sync::Arc;

	use super::{mock::*, *};
	use mock::run_to_block_and_drain_pool;
	use remote_externalities::{Mode, OnlineConfig};
	use sp_runtime::traits::Bounded;

	// we only use the hash type from this (I hope).
	type Block = sp_runtime::testing::Block<Extrinsic>;

	#[tokio::test]
	async fn on_initialize_migration() {
		sp_tracing::try_init_simple();
		let run_with_limits = |limits| async move {
			let mut ext = remote_externalities::Builder::<Block>::new()
				.mode(Mode::Online(OnlineConfig {
					transport: std::env!("WS_API").to_owned().into(),
					scrape_children: true,
					..Default::default()
				}))
				.state_version(sp_core::StateVersion::V0)
				.build()
				.await
				.unwrap();

			ext.execute_with(|| {
				// requires the block number type in our tests to be same as with mainnet, u32.
				let mut now = frame_system::Pallet::<Test>::block_number();
				let mut duration = 0;
				AutoLimits::<Test>::put(Some(limits));
				loop {
					run_to_block(now + 1);
					if StateTrieMigration::migration_process().finished() {
						break
					}
					duration += 1;
					now += 1;
				}

				log::info!(
					target: LOG_TARGET,
					"finished on_initialize migration in {} block, final state of the task: {:?}",
					duration,
					StateTrieMigration::migration_process()
				);
			})
		};
		// item being the bottleneck
		run_with_limits(MigrationLimits { item: 1000, size: 4 * 1024 * 1024 }).await;
		// size being the bottleneck
		run_with_limits(MigrationLimits { item: Bounded::max_value(), size: 4 * 1024 }).await;
	}

	#[tokio::test]
	async fn offchain_worker_migration() {
		sp_tracing::try_init_simple();
		let run_with_limits = |limits| async move {
			let mut ext = remote_externalities::Builder::<Block>::new()
				.mode(Mode::Online(OnlineConfig {
					transport: std::env!("WS_API").to_owned().into(),
					scrape_children: true,
					state_snapshot: Some(
						"/home/kianenigma/remote-builds/ksm-state".to_owned().into(),
					),
					..Default::default()
				}))
				.state_version(sp_core::StateVersion::V0)
				.build()
				.await
				.unwrap();
			let pool_state = offchainify(&mut ext);

			ext.execute_with(|| {
				// requires the block number type in our tests to be same as with mainnet, u32.
				let mut now = frame_system::Pallet::<Test>::block_number();
				let mut duration = 0;
				UnsignedLimits::<Test>::put(Some(limits));
				loop {
					run_to_block_and_drain_pool(now + 1, Arc::clone(&pool_state));
					if StateTrieMigration::migration_process().finished() {
						break
					}
					duration += 1;
					now += 1;
				}

				log::info!(
					target: LOG_TARGET,
					"finished offchain-worker migration in {} block, final state of the task: {:?}",
					duration,
					StateTrieMigration::migration_process()
				);
			})
		};
		// item being the bottleneck
		// run_with_limits(MigrationLimits { item: 1000, size: 4 * 1024 * 1024 }).await;
		// size being the bottleneck
		run_with_limits(MigrationLimits { item: Bounded::max_value(), size: 2 * 1024 * 1024 })
			.await;
	}
}
