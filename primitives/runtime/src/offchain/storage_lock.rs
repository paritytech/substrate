// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! # Off-chain Storage Lock
//!
//! A storage-based lock with a defined expiry time.
//!
//! The lock is using Local Storage and allows synchronizing access to critical
//! section of your code for concurrently running Off-chain Workers. Usage of
//! `PERSISTENT` variant of the storage persists the lock value across a full node
//! restart or re-orgs.
//!
//! A use case for the lock is to make sure that a particular section of the
//! code is only run by one Off-chain Worker at a time. This may include
//! performing a side-effect (i.e. an HTTP call) or alteration of single or
//! multiple Local Storage entries.
//!
//! One use case would be collective updates of multiple data items or append /
//! remove of i.e. sets, vectors which are stored in the off-chain storage DB.
//!
//! ## Example:
//!
//! ```rust
//! # use codec::{Decode, Encode, Codec};
//! // in your off-chain worker code
//! use sp_runtime::offchain::{
//!		storage::StorageValueRef,
//!		storage_lock::{StorageLock, Time},
//! };
//!
//! fn append_to_in_storage_vec<'a, T>(key: &'a [u8], _: T) where T: Codec {
//!    // `access::lock` defines the storage entry which is used for
//!    // persisting the lock in the underlying database.
//!    // The entry name _must_ be unique and can be interpreted as a
//!    // unique mutex instance reference tag.
//!    let mut lock = StorageLock::<Time>::new(b"access::lock");
//!    {
//!         let _guard = lock.lock();
//!         let acc = StorageValueRef::persistent(key);
//!         let v: Vec<T> = acc.get::<Vec<T>>().unwrap().unwrap();
//!         // modify `v` as desired
//!         // i.e. perform some heavy computation with
//!         // side effects that should only be done once.
//!         acc.set(&v);
//!         // drop `_guard` implicitly at end of scope
//!    }
//! }
//! ```

use crate::offchain::storage::StorageValueRef;
use crate::traits::AtLeast32BitUnsigned;
use codec::{Codec, Decode, Encode};
use sp_core::offchain::{Duration, Timestamp};
use sp_io::offchain;

/// Default expiry duration for time based locks in milliseconds.
const STORAGE_LOCK_DEFAULT_EXPIRY_DURATION: Duration = Duration::from_millis(20_000);

/// Default expiry duration for block based locks in blocks.
const STORAGE_LOCK_DEFAULT_EXPIRY_BLOCKS: u32 = 4;

/// Time between checks if the lock is still being held in milliseconds.
const STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE_MIN: Duration = Duration::from_millis(100);
const STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE_MAX: Duration = Duration::from_millis(10);

/// Lockable item for use with a persisted storage lock.
///
/// Bound for an item that has a stateful ordered meaning
/// without explicitly requiring `Ord` trait in general.
pub trait Lockable: Sized {
	/// An instant type specifying i.e. a point in time.
	type Deadline: Sized + Codec + Clone;

	/// Calculate the deadline based on a current state
	/// such as time or block number and derives the deadline.
	fn deadline(&self) -> Self::Deadline;

	/// Verify the deadline has not expired compared to the
	/// current state, i.e. time or block number.
	fn has_expired(deadline: &Self::Deadline) -> bool;

	/// Snooze at least until `deadline` is reached.
	///
	/// Note that `deadline` is only passed to allow optimizations
	/// for `Lockables` which have a time based component.
	fn snooze(_deadline: &Self::Deadline) {
		sp_io::offchain::sleep_until(
			offchain::timestamp().add(STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE_MAX),
		);
	}
}

/// Lockable based on the current timestamp with a configurable expiration time.
#[derive(Encode, Decode)]
pub struct Time {
	/// How long the lock will stay valid once `fn lock(..)` or
	/// `fn try_lock(..)` successfully acquire a lock.
	expiration_duration: Duration,
}

impl Default for Time {
	fn default() -> Self {
		Self {
			expiration_duration: STORAGE_LOCK_DEFAULT_EXPIRY_DURATION,
		}
	}
}

impl Lockable for Time {
	type Deadline = Timestamp;

	fn deadline(&self) -> Self::Deadline {
		offchain::timestamp().add(self.expiration_duration)
	}

	fn has_expired(deadline: &Self::Deadline) -> bool {
		offchain::timestamp() > *deadline
	}

	fn snooze(deadline: &Self::Deadline) {
		let now = offchain::timestamp();
		let remainder: Duration = now.diff(&deadline);
		// do not snooze the full duration, but instead snooze max 100ms
		// it might get unlocked in another thread
		use core::cmp::{max, min};
		let snooze = max(
			min(remainder, STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE_MAX),
			STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE_MIN,
		);
		sp_io::offchain::sleep_until(now.add(snooze));
	}
}

/// A deadline based on block number and time.
#[derive(Encode, Decode, Eq, PartialEq)]
pub struct BlockAndTimeDeadline<B: BlockNumberProvider> {
	/// The block number until which the lock is still valid _at least_.
	pub block_number: <B as BlockNumberProvider>::BlockNumber,
	/// The timestamp until which the lock is still valid _at least_.
	pub timestamp: Timestamp,
}

impl<B: BlockNumberProvider> Clone for BlockAndTimeDeadline<B> {
	fn clone(&self) -> Self {
		Self {
			block_number: self.block_number.clone(),
			timestamp: self.timestamp.clone(),
		}
	}
}

impl<B: BlockNumberProvider> Default for BlockAndTimeDeadline<B> {
	/// Provide the current state of block number and time.
	fn default() -> Self {
		Self {
			block_number: B::current_block_number() + STORAGE_LOCK_DEFAULT_EXPIRY_BLOCKS.into(),
			timestamp: offchain::timestamp().add(STORAGE_LOCK_DEFAULT_EXPIRY_DURATION),
		}
	}
}

/// Lockable based on block number and timestamp.
///
/// Expiration is defined if both, block number _and_ timestamp
/// expire.
pub struct BlockAndTime<B: BlockNumberProvider> {
	/// Relative block number offset, which is used to determine
	/// the block number part of the deadline.
	expiration_block_number_offset: u32,
	/// Relative duration, used to derive the time based part of
	/// the deadline.
	expiration_duration: Duration,

	_phantom: core::marker::PhantomData<B>,
}

impl<B: BlockNumberProvider> Default for BlockAndTime<B> {
	fn default() -> Self {
		Self {
			expiration_block_number_offset: STORAGE_LOCK_DEFAULT_EXPIRY_BLOCKS,
			expiration_duration: STORAGE_LOCK_DEFAULT_EXPIRY_DURATION,
			_phantom: core::marker::PhantomData::<B>,
		}
	}
}

// derive not possible, since `B` does not necessarily implement `trait Clone`
impl<B: BlockNumberProvider> Clone for BlockAndTime<B> {
	fn clone(&self) -> Self {
		Self {
			expiration_block_number_offset: self.expiration_block_number_offset.clone(),
			expiration_duration: self.expiration_duration,
			_phantom: core::marker::PhantomData::<B>,
		}
	}
}

impl<B: BlockNumberProvider> Lockable for BlockAndTime<B> {
	type Deadline = BlockAndTimeDeadline<B>;

	fn deadline(&self) -> Self::Deadline {
		let block_number = <B as BlockNumberProvider>::current_block_number()
			+ self.expiration_block_number_offset.into();
		BlockAndTimeDeadline {
			timestamp: offchain::timestamp().add(self.expiration_duration),
			block_number,
		}
	}

	fn has_expired(deadline: &Self::Deadline) -> bool {
		offchain::timestamp() > deadline.timestamp
			&& <B as BlockNumberProvider>::current_block_number() > deadline.block_number
	}

	fn snooze(deadline: &Self::Deadline) {
		let now = offchain::timestamp();
		let remainder: Duration = now.diff(&(deadline.timestamp));
		use core::cmp::{max, min};
		let snooze = max(
			min(remainder, STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE_MAX),
			STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE_MIN,
		);
		sp_io::offchain::sleep_until(now.add(snooze));
	}
}

/// Storage based lock.
///
/// A lock that is persisted in the DB and provides the ability to guard against
/// concurrent access in an off-chain worker, with a defined expiry deadline
/// based on the concrete [`Lockable`](Lockable) implementation.
pub struct StorageLock<'a, L = Time> {
	// A storage value ref which defines the DB entry representing the lock.
	value_ref: StorageValueRef<'a>,
	lockable: L,
}

impl<'a, L: Lockable + Default> StorageLock<'a, L> {
	/// Create a new storage lock with a `default()` instance of type `L`.
	pub fn new(key: &'a [u8]) -> Self {
		Self::with_lockable(key, Default::default())
	}
}

impl<'a, L: Lockable> StorageLock<'a, L> {
	/// Create a new storage lock with an explicit instance of a lockable `L`.
	pub fn with_lockable(key: &'a [u8], lockable: L) -> Self {
		Self {
			value_ref: StorageValueRef::<'a>::persistent(key),
			lockable,
		}
	}

	/// Extend active lock's deadline
	fn extend_active_lock(&mut self) -> Result<<L as Lockable>::Deadline, ()> {
		let res = self.value_ref.mutate(|s: Option<Option<L::Deadline>>| -> Result<<L as Lockable>::Deadline, ()> {
			match s {
				// lock is present and is still active, extend the lock.
				Some(Some(deadline)) if !<L as Lockable>::has_expired(&deadline) =>
					Ok(self.lockable.deadline()),
				// other cases
				_ => Err(()),
			}
		});
		match res {
			Ok(Ok(deadline)) => Ok(deadline),
			Ok(Err(_)) => Err(()),
			Err(e) => Err(e),
		}
	}

	/// Internal lock helper to avoid lifetime conflicts.
	fn try_lock_inner(
		&mut self,
		new_deadline: L::Deadline,
	) -> Result<(), <L as Lockable>::Deadline> {
		let res = self.value_ref.mutate(
			|s: Option<Option<L::Deadline>>|
			-> Result<<L as Lockable>::Deadline, <L as Lockable>::Deadline> {
				match s {
					// no lock set, we can safely acquire it
					None => Ok(new_deadline),
					// write was good, but read failed
					Some(None) => Ok(new_deadline),
					// lock is set, but it is expired. We can re-acquire it.
					Some(Some(deadline)) if <L as Lockable>::has_expired(&deadline) =>
						Ok(new_deadline),
					// lock is present and is still active
					Some(Some(deadline)) => Err(deadline),
				}
			},
		);
		match res {
			Ok(Ok(_)) => Ok(()),
			Ok(Err(deadline)) => Err(deadline),
			Err(e) => Err(e),
		}
	}

	/// A single attempt to lock using the storage entry.
	///
	/// Returns a lock guard on success, otherwise an error containing the
	/// `<Self::Lockable>::Deadline` in for the currently active lock
	/// by another task `Err(<L as Lockable>::Deadline)`.
	pub fn try_lock(&mut self) -> Result<StorageLockGuard<'a, '_, L>, <L as Lockable>::Deadline> {
		self.try_lock_inner(self.lockable.deadline())?;
		Ok(StorageLockGuard::<'a, '_> { lock: Some(self) })
	}

	/// Repeated lock attempts until the lock is successfully acquired.
	///
	/// If one uses `fn forget(..)`, it is highly likely `fn try_lock(..)`
	/// is the correct API to use instead of `fn lock(..)`, since that might
	/// never unlock in the anticipated span i.e. when used with `BlockAndTime`
	/// during a certain block number span.
	pub fn lock(&mut self) -> StorageLockGuard<'a, '_, L> {
		while let Err(deadline) = self.try_lock_inner(self.lockable.deadline()) {
			L::snooze(&deadline);
		}
		StorageLockGuard::<'a, '_, L> { lock: Some(self) }
	}

	/// Explicitly unlock the lock.
	fn unlock(&mut self) {
		self.value_ref.clear();
	}
}

/// RAII style guard for a lock.
pub struct StorageLockGuard<'a, 'b, L: Lockable> {
	lock: Option<&'b mut StorageLock<'a, L>>,
}

impl<'a, 'b, L: Lockable> StorageLockGuard<'a, 'b, L> {
	/// Consume the guard but **do not** unlock the underlying lock.
	///
	/// Can be used to implement a grace period after doing some
	/// heavy computations and sending a transaction to be included
	/// on-chain. By forgetting the lock, it will stay locked until
	/// its expiration deadline is reached while the off-chain worker
	/// can already exit.
	pub fn forget(mut self) {
		let _ = self.lock.take();
	}

	/// Extend the lock by guard deadline if it already exists.
	///
	/// i.e. large sets of items for which it is hard to calculate a
	/// meaning full conservative deadline which does not block for a
	/// very long time on node termination.
	pub fn extend_lock(&mut self) -> Result<<L as Lockable>::Deadline, ()> {
		if let Some(ref mut lock) = self.lock {
			lock.extend_active_lock()
		} else {
			Err(())
		}
	}
}

impl<'a, 'b, L: Lockable> Drop for StorageLockGuard<'a, 'b, L> {
	fn drop(&mut self) {
		if let Some(lock) = self.lock.take() {
			lock.unlock();
		}
	}
}

impl<'a> StorageLock<'a, Time> {
	/// Explicitly create a time based storage lock with a non-default
	/// expiration timeout.
	pub fn with_deadline(key: &'a [u8], expiration_duration: Duration) -> Self {
		Self {
			value_ref: StorageValueRef::<'a>::persistent(key),
			lockable: Time {
				expiration_duration: expiration_duration,
			},
		}
	}
}

impl<'a, B> StorageLock<'a, BlockAndTime<B>>
where
	B: BlockNumberProvider,
{
	/// Explicitly create a time and block number based storage lock with
	/// a non-default expiration duration and block number offset.
	pub fn with_block_and_time_deadline(
		key: &'a [u8],
		expiration_block_number_offset: u32,
		expiration_duration: Duration,
	) -> Self {
		Self {
			value_ref: StorageValueRef::<'a>::persistent(key),
			lockable: BlockAndTime::<B> {
				expiration_block_number_offset,
				expiration_duration,
				_phantom: core::marker::PhantomData,
			},
		}
	}

	/// Explicitly create a time and block number based storage lock with
	/// the default expiration duration and a non-default block number offset.
	pub fn with_block_deadline(key: &'a [u8], expiration_block_number_offset: u32) -> Self {
		Self {
			value_ref: StorageValueRef::<'a>::persistent(key),
			lockable: BlockAndTime::<B> {
				expiration_block_number_offset,
				expiration_duration: STORAGE_LOCK_DEFAULT_EXPIRY_DURATION,
				_phantom: core::marker::PhantomData,
			},
		}
	}
}

/// Bound for a block number source
/// used with [`BlockAndTime<BlockNumberProvider>`](BlockAndTime).
pub trait BlockNumberProvider {
	/// Type of `BlockNumber` to provide.
	type BlockNumber: Codec + Clone + Ord + Eq + AtLeast32BitUnsigned;
	/// Returns the current block number.
	///
	/// Provides an abstraction over an arbitrary way of providing the
	/// current block number.
	///
	/// In case of using crate `sp_runtime` without the crate `frame`
	/// system, it is already implemented for
	/// `frame_system::Module<T: Config>` as:
	///
	/// ```ignore
	/// fn current_block_number() -> Self {
	///     frame_system::Module<Config>::block_number()
	/// }
	/// ```
	/// .
	fn current_block_number() -> Self::BlockNumber;
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::offchain::{testing, OffchainWorkerExt, OffchainDbExt};
	use sp_io::TestExternalities;

	const VAL_1: u32 = 0u32;
	const VAL_2: u32 = 0xFFFF_FFFFu32;

	#[test]
	fn storage_lock_write_unlock_lock_read_unlock() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainDbExt::new(offchain.clone()));
		t.register_extension(OffchainWorkerExt::new(offchain));

		t.execute_with(|| {
			let mut lock = StorageLock::<'_, Time>::new(b"lock_1");

			let val = StorageValueRef::persistent(b"protected_value");

			{
				let _guard = lock.lock();

				val.set(&VAL_1);

				assert_eq!(val.get::<u32>(), Some(Some(VAL_1)));
			}

			{
				let _guard = lock.lock();
				val.set(&VAL_2);

				assert_eq!(val.get::<u32>(), Some(Some(VAL_2)));
			}
		});
		// lock must have been cleared at this point
		assert_eq!(state.read().persistent_storage.get(b"lock_1"), None);
	}

	#[test]
	fn storage_lock_and_forget() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainDbExt::new(offchain.clone()));
		t.register_extension(OffchainWorkerExt::new(offchain));

		t.execute_with(|| {
			let mut lock = StorageLock::<'_, Time>::new(b"lock_2");

			let val = StorageValueRef::persistent(b"protected_value");

			let guard = lock.lock();

			val.set(&VAL_1);

			assert_eq!(val.get::<u32>(), Some(Some(VAL_1)));

			guard.forget();
		});
		// lock must have been cleared at this point
		let opt = state.read().persistent_storage.get(b"lock_2");
		assert!(opt.is_some());
	}

	#[test]
	fn storage_lock_and_let_expire_and_lock_again() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainDbExt::new(offchain.clone()));
		t.register_extension(OffchainWorkerExt::new(offchain));

		t.execute_with(|| {
			let sleep_until = offchain::timestamp().add(Duration::from_millis(500));
			let lock_expiration = Duration::from_millis(200);

			let mut lock = StorageLock::<'_, Time>::with_deadline(b"lock_3", lock_expiration);

			{
				let guard = lock.lock();
				guard.forget();
			}

			// assure the lock expires
			offchain::sleep_until(sleep_until);

			let mut lock = StorageLock::<'_, Time>::new(b"lock_3");
			let res = lock.try_lock();
			assert!(res.is_ok());
			let guard = res.unwrap();
			guard.forget();
		});

		// lock must have been cleared at this point
		let opt = state.read().persistent_storage.get(b"lock_3");
		assert!(opt.is_some());
	}

	#[test]
	fn extend_active_lock() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainDbExt::new(offchain.clone()));
		t.register_extension(OffchainWorkerExt::new(offchain));

		t.execute_with(|| {
			let lock_expiration = Duration::from_millis(300);

			let mut lock = StorageLock::<'_, Time>::with_deadline(b"lock_4", lock_expiration);
			let mut guard = lock.lock();

			// sleep_until < lock_expiration
			offchain::sleep_until(offchain::timestamp().add(Duration::from_millis(200)));

			// the lock is still active, extend it successfully
			assert_eq!(guard.extend_lock().is_ok(), true);

			// sleep_until < deadline
			offchain::sleep_until(offchain::timestamp().add(Duration::from_millis(200)));

			// the lock is still active, try_lock will fail
			let mut lock = StorageLock::<'_, Time>::with_deadline(b"lock_4", lock_expiration);
			let res = lock.try_lock();
			assert_eq!(res.is_ok(), false);

			// sleep again untill sleep_until > deadline
			offchain::sleep_until(offchain::timestamp().add(Duration::from_millis(200)));

			// the lock has expired, failed to extend it
			assert_eq!(guard.extend_lock().is_ok(), false);
			guard.forget();

			// try_lock will succeed
			let mut lock = StorageLock::<'_, Time>::with_deadline(b"lock_4", lock_expiration);
			let res = lock.try_lock();
			assert!(res.is_ok());
			let guard = res.unwrap();

			guard.forget();
		});

		// lock must have been cleared at this point
		let opt = state.read().persistent_storage.get(b"lock_4");
		assert_eq!(opt.unwrap(), vec![132_u8, 3u8, 0, 0, 0, 0, 0, 0]); // 132 + 256 * 3 = 900
	}
}
