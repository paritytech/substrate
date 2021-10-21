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
//! upgrading a chain to `StorageVersion::V2`, where all keys need to be touched.
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
//! amount, yet the do impose some work on the validators/collators.
//!
//! ### Signed migration
//!
//! as a backup, the migration process can be set in motion via signed transactions that basically
//! say in advance how many items and how many bytes they will consume, and pay for it as well. This
//! can be a good safe alternative, if the former two systems are not desirable.
//!
//! The (minor) caveat of this approach is that we cannot know in advance how many bytes reading a
//! certain number of keys will incur. To overcome this, the runtime needs to configure this pallet
//! with a `SignedDepositPerItem`. This is be per-item deposit that the origin of the signed
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
	use frame_benchmarking::Zero;
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
	use sp_core::storage::well_known_keys::CHILD_STORAGE_KEY_PREFIX;
	use sp_runtime::traits::{Bounded, Saturating};
	use sp_std::prelude::*;

	pub(crate) type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

	pub trait WeightInfo {
		fn process_top_key(x: u32) -> Weight;
	}
	impl WeightInfo for () {
		fn process_top_key(x: u32) -> Weight {
			1000000
		}
	}

	/// A migration task stored in state.
	///
	/// It tracks the last top and child keys read.
	#[derive(Clone, Encode, Decode, scale_info::TypeInfo)]
	#[codec(mel_bound(T: Config))]
	#[scale_info(skip_type_params(T))]
	#[cfg_attr(test, derive(PartialEq, Eq))]
	pub struct MigrationTask<T: Config> {
		/// The top key that we currently have to iterate.
		///
		/// If it does not exist, it means that the migration is done and no further keys exist.
		pub(crate) current_top: Option<Vec<u8>>,
		/// The last child key that we have processed.
		///
		/// This is a child key under the current `self.last_top`.
		///
		/// If this is set, no further top keys are processed until the child key migration is
		/// complete.
		pub(crate) current_child: Option<Vec<u8>>,

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

		#[codec(skip)]
		_ph: sp_std::marker::PhantomData<T>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> sp_std::fmt::Debug for MigrationTask<T> {
		fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
			f.debug_struct("MigrationTask")
				.field(
					"top",
					&self.current_top.as_ref().map(|d| sp_core::hexdisplay::HexDisplay::from(d)),
				)
				.field(
					"child",
					&self.current_child.as_ref().map(|d| sp_core::hexdisplay::HexDisplay::from(d)),
				)
				.field("dyn_top_items", &self.dyn_top_items)
				.field("dyn_child_items", &self.dyn_child_items)
				.field("dyn_size", &self.dyn_size)
				.finish()
		}
	}

	impl<T: Config> Default for MigrationTask<T> {
		fn default() -> Self {
			Self {
				current_top: Some(Default::default()),
				current_child: Default::default(),
				dyn_child_items: Default::default(),
				dyn_top_items: Default::default(),
				dyn_size: Default::default(),
				_ph: Default::default(),
			}
		}
	}

	impl<T: Config> MigrationTask<T> {
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
			loop {
				self.migrate_tick();
				if self.exhausted(limits) {
					break
				}
			}
		}

		/// Check if there's any work left, or if we have exhausted the limits already.
		fn exhausted(&self, limits: MigrationLimits) -> bool {
			self.current_top.is_none() ||
				self.dyn_total_items() >= limits.item ||
				self.dyn_size >= limits.size
		}

		/// Migrate AT MOST ONE KEY. This can be either a top or a child key.
		///
		/// The only exception to this is that when the last key of the child tree is migrated, then
		/// the top tree under which the child tree lives is also migrated.
		///
		/// This function is the core of this entire pallet.
		fn migrate_tick(&mut self) {
			match (self.current_top.as_ref(), self.current_child.as_ref()) {
				(Some(_), Some(_)) => {
					// we're in the middle of doing work on a child tree.
					self.migrate_child();
					if self.current_child.is_none() {
						// this is the end of this child trie. process the top trie as well.
						self.migrate_top()
					}
				},
				(Some(ref top_key), None) => {
					if top_key.starts_with(CHILD_STORAGE_KEY_PREFIX) {
						// no child migration at hand, but one will begin here.
						self.current_child = Some(vec![]);
						self.migrate_child();
						if self.current_child.is_none() {
							// this is the end of this child trie. process the top trie as well.
							self.migrate_top()
						}
					} else {
						self.migrate_top();
					}
				},
				(None, Some(_)) => {
					// TODO: test edge case: last top key has child
					log!(error, "LOGIC ERROR: unreachable code.");
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
			let current_child =
				self.current_child.clone().expect("value checked to be `Some`; qed");
			let current_top = self.current_top.clone().expect("value checked to be `Some`; qed");

			let child_key = Pallet::<T>::child_io_key(&current_child);
			if let Some(data) = sp_io::default_child_storage::get(child_key, &current_top) {
				self.dyn_size = self.dyn_size.saturating_add(data.len() as u32);
				sp_io::default_child_storage::set(child_key, &current_top, &data)
			}
			self.dyn_child_items.saturating_inc();
			let next_key = sp_io::default_child_storage::next_key(child_key, &current_top);
			self.current_child = next_key;
			log!(
				trace,
				"migrating child key {:?} from top key {:?}, next task: {:?}",
				sp_core::hexdisplay::HexDisplay::from(&current_child),
				sp_core::hexdisplay::HexDisplay::from(&current_top),
				self
			);
		}

		/// Migrate the current top key, setting it to its new value, if one exists.
		///
		/// It updates the dynamic counters.
		fn migrate_top(&mut self) {
			let current_top = self.current_top.clone().expect("value checked to be `Some`; qed");
			if let Some(data) = sp_io::storage::get(&current_top) {
				self.dyn_size = self.dyn_size.saturating_add(data.len() as u32);
				sp_io::storage::set(&current_top, &data);
			}
			self.dyn_top_items.saturating_inc();
			let next_key = sp_io::storage::next_key(&current_top);
			self.current_top = next_key;
			log!(
				trace,
				"migrated top key {:?}, next task: {:?}",
				sp_core::hexdisplay::HexDisplay::from(&current_top),
				self
			);
		}
	}

	/// The limits of a migration.
	#[derive(Clone, Copy, Encode, Decode, scale_info::TypeInfo, Default, Debug, PartialEq, Eq)]
	pub struct MigrationLimits {
		/// The byte size limit.
		pub(crate) size: u32,
		/// The number of keys limit.
		pub(crate) item: u32,
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

		/// The weight information of this pallet.
		type WeightInfo: WeightInfo;

		/// The priority used for unsigned transactions.
		type Priority: Get<TransactionPriority>;
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
	/// 1. be large enough to accommodate things like `:code:`
	/// 2. small enough to never brick a parachain due to PoV limits.
	///
	/// if set to `None`, then no unsigned migration happens.
	#[pallet::storage]
	#[pallet::getter(fn unsigned_size_limit)]
	pub type UnsignedSizeLimit<T> = StorageValue<_, Option<u32>, ValueQuery>;

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
				maybe_config.is_some() ^ Self::unsigned_size_limit().is_some(),
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
			maybe_size_limit: Option<u32>,
		) -> DispatchResultWithPostInfo {
			T::ControlOrigin::ensure_origin(origin)?;
			ensure!(
				maybe_size_limit.is_some() ^ Self::auto_limits().is_some(),
				"unsigned and auto migration cannot co-exist"
			);
			UnsignedSizeLimit::<T>::put(maybe_size_limit);
			Ok(().into())
		}

		/// The unsigned call that can be submitted by offchain workers.
		///
		/// This can only be valid if it is generated from the local node, which means only
		/// validators can generate this call.
		///
		/// It is guaranteed that migrating `item_limit` will not cause the total read bytes to
		/// exceed [`UnsignedSizeLimit`].
		///
		/// The `size_limit` in the call arguments is for weighing. THe `_task` argument in the call
		/// is for validation and ensuring that the migration process has not ticked forward since
		/// the call was generated.
		#[pallet::weight(Pallet::<T>::dynamic_weight(*item_limit, *witness_size_limit))]
		pub fn continue_migrate_unsigned(
			origin: OriginFor<T>,
			item_limit: u32,
			witness_size_limit: u32,
			_witness_task: MigrationTask<T>,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;
			let unsigned_size_limit =
				Self::unsigned_size_limit().ok_or("unsigned limit not set, tx not allowed.")?;
			ensure!(witness_size_limit == unsigned_size_limit, "wrong size limit witness data");

			let mut task = Self::migration_process();
			// pre-dispatch and validate-unsigned already assure this.
			debug_assert_eq!(task, _witness_task);

			let limits = MigrationLimits { size: unsigned_size_limit, item: item_limit };
			task.migrate_until_exhaustion(limits);

			// we panic if the validator submitted a bad transaction, making it financially bad for
			// them to cheat. We could relax this. Also, if a bug causes validators to mistakenly
			// produce bad transactions, they can avoid it by disabling offchain workers.
			assert!(task.dyn_size < unsigned_size_limit);

			Self::deposit_event(Event::<T>::Migrated(
				task.dyn_top_items,
				task.dyn_child_items,
				MigrationCompute::Unsigned,
			));

			Ok(().into())
		}

		/// Migrate AT MOST `item_limit` keys by reading and writing them.
		///
		/// The dispatch origin of this call can be any signed account.
		///
		/// This transaction has NO MONETARY INCENTIVES. calling it will only incur transaction fees
		/// on the caller, with no rewards paid out.
		///
		/// The sum of the byte length of all the data read must be provided for up-front
		/// fee-payment and weighing.
		#[pallet::weight(Pallet::<T>::dynamic_weight(*item_limit, *size_limit))]
		pub fn continue_migrate(
			origin: OriginFor<T>,
			item_limit: u32,
			size_limit: u32,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;

			// ensure they can pay more than the fee.
			let deposit = T::SignedDepositPerItem::get().saturating_mul(item_limit.into());
			ensure!(T::Currency::can_slash(&who, deposit), "not enough funds");

			let mut task = Self::migration_process();
			task.migrate_until_exhaustion(MigrationLimits { size: size_limit, item: item_limit });

			// ensure that the migration witness data was correct.
			if item_limit != task.dyn_total_items() || size_limit != task.dyn_size {
				// let the imbalance burn.
				let (_imbalance, _remainder) = T::Currency::slash(&who, deposit);
				// defensive.
				debug_assert!(_remainder.is_zero());
				return Err("Wrong witness data".into())
			}

			Self::deposit_event(Event::<T>::Migrated(
				task.dyn_top_items,
				task.dyn_child_items,
				MigrationCompute::Signed,
			));
			MigrationProcess::<T>::put(task);
			Ok(().into())
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
					sp_io::default_child_storage::get(Self::child_io_key(child_key), &top_key)
				{
					dyn_size = dyn_size.saturating_add(data.len() as u32);
					sp_io::default_child_storage::set(
						Self::child_io_key(child_key),
						&top_key,
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

		fn offchain_worker(_: BlockNumberFor<T>) {
			if let Some(unsigned_size_limit) = Self::unsigned_size_limit() {
				let mut task = Self::migration_process();
				let limits =
					MigrationLimits { size: unsigned_size_limit, item: Bounded::max_value() };
				task.migrate_until_exhaustion(limits);

				// the last item cause us to go beyond the size limit, so we subtract one. we are
				// making this assumption based on the impl of `migrate_until_exhaustion`.
				let safe_items_to_read = task.dyn_total_items().saturating_sub(1);

				let original_task = Self::migration_process();
				let call = Call::continue_migrate_unsigned {
					item_limit: safe_items_to_read,
					// note that this must be simply the limit, not the actual bytes read.
					witness_size_limit: unsigned_size_limit,
					witness_task: original_task,
				};
				match SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into()) {
					Ok(_) => {
						log!(
							debug,
							"submitted a call to migrate {} items of {} bytes.",
							safe_items_to_read,
							task.dyn_size
						)
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
					.priority(T::Priority::get())
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
			UnsignedSizeLimit::<T>::kill();
			AutoLimits::<T>::kill();
		}

		fn child_io_key(storage_key: &Vec<u8>) -> &[u8] {
			use sp_core::storage::{ChildType, PrefixedStorageKey};
			match ChildType::from_prefixed_key(PrefixedStorageKey::new_ref(storage_key)) {
				Some((ChildType::ParentKeyId, storage_key)) => storage_key,
				None => &[], // Ignore TODO
			}
		}
	}
}

#[cfg(feature = "runtime-benchmarks")]
mod benchmarks {
	use super::*;
	use sp_std::prelude::*;

	const KEY: &'static [u8] = b"key";

	frame_benchmarking::benchmarks! {
		process_top_key {
			let x in 1 .. (4 * 1024 * 1024);
			sp_io::storage::set(KEY, &vec![1u8; x as usize]);
		}: {
			let data = sp_io::storage::get(KEY).unwrap();
			sp_io::storage::set(KEY, &vec![1u8; x as usize]);
			let _next = sp_io::storage::next_key(KEY);
			assert_eq!(data.len(), x as usize);
		}
	}
}

#[cfg(test)]
mod mock {
	use super::*;
	use crate as pallet_state_trie_migration;
	use frame_support::{parameter_types, traits::Hooks};
	use frame_system::EnsureRoot;
	use sp_core::H256;
	use sp_runtime::{
		testing::Header,
		traits::{BlakeTwo256, IdentityLookup},
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
		pub const BlockHashCount: u64 = 250;
		pub const SS58Prefix: u8 = 42;
	}

	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type Origin = Origin;
		type Call = Call;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
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
		type SignedDepositPerItem = ();
		type WeightInfo = ();
		type Priority = ();
	}

	impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Test
	where
		Call: From<LocalCall>,
	{
		type OverarchingCall = Call;
		type Extrinsic = Extrinsic;
	}

	pub type Extrinsic = sp_runtime::testing::TestXt<Call, ()>;

	pub fn new_test_ext() -> sp_io::TestExternalities {
		use sp_core::storage::ChildInfo;

		let t = frame_system::GenesisConfig::default();
		let mut storage = sp_core::storage::Storage {
			top: vec![
				(b"key1".to_vec(), vec![1u8; 10]), // 6b657931
				(b"key2".to_vec(), vec![2u8; 20]), // 6b657932
				(b"key3".to_vec(), vec![3u8; 30]), // 6b657934
				(b"key4".to_vec(), vec![4u8; 40]), // 6b657934
				(sp_core::storage::well_known_keys::CODE.to_vec(), vec![1u8; 100]),
			]
			.into_iter()
			.collect(),
			children_default: vec![
				(
					b":child_storage:chk1".to_vec(),
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
					b":child_storage:chk2".to_vec(),
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
		t.assimilate_storage::<Test>(&mut storage).unwrap();
		sp_tracing::try_init_simple();

		(storage, StateVersion::V0).into()
	}

	pub fn run_to_block(n: u64) {
		while System::block_number() < n {
			System::set_block_number(System::block_number() + 1);
			System::on_initialize(System::block_number());
			StateTrieMigration::on_initialize(System::block_number());

			System::on_finalize(System::block_number());
		}
	}
}

#[cfg(test)]
mod test {
	use super::{mock::*, *};

	#[test]
	fn auto_migrate_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(AutoLimits::<Test>::get(), None);
			assert_eq!(MigrationProcess::<Test>::get(), Default::default());

			// nothing happens if we don't set the limits.
			run_to_block(50);
			assert_eq!(MigrationProcess::<Test>::get(), Default::default());

			// this should allow 1 item per block to be migrated.
			AutoLimits::<Test>::put(Some(MigrationLimits { item: 1, size: 150 }));

			run_to_block(80);
		})
	}

	#[test]
	fn unsigned_migration_works() {
		todo!();
	}

	#[test]
	fn manual_migrate_works() {
		todo!("test manually signed migration");
	}

	#[test]
	fn custom_migrate_works() {
		todo!("test custom keys to be migrated via signed")
	}
}
