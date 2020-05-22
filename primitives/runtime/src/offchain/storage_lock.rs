// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! # Offchain Storage Lock
//!
//! A storage-based lock with a defined expiry time.
//!
//! The lock is using Local Storage and allows synchronizing access to critical
//! section of your code for concurrently running Off-chain Workers. Usage of
//! `PERSISTENT` variant of the storage persists the lock value accross a full node
//! restart or re-orgs.
//!
//! A use case for the lock is to make sure that a particular section of the
//! code is only run by one Off-chain Worker at the time. This may include
//! performing a side-effect (i.e. an HTTP call) or alteration of single or
//! multiple Local Storage entries.
//!
//! One use case would be collective updates of multiple data items or append /
//! remove of i.e. sets, vectors which are stored in the offchain storage DB.
//!
//! ## Example:
//!
//! ```rust
//! # use crate::offchain::storage::StorageValueRef;
//! # use codec::{Decode, Encode, Codec};
//! // in your off-chain worker code
//!
//! fn append_to_in_storage_vec<'a, T>(key: &'a [u8], _: T) where T: Encode {
//!    // `access::lock` defines the storage entry which is used for
//!    // persisting the lock in the underlying database.
//!    // The entry name _must_ be unique and can be seen as mutex instance reference.
//!    let mut lock = StorageLock::new(b"access::lock");
//!    {
//!         let _guard = lock.spin_lock();
//!         let acc = StorageValueRef::persistent(key);
//!         let v: Vec<T> = acc.get::<Vec<T>>().unwrap().unwrap();
//!         // modify `v` as desired
//!         // i.e. perform some heavy computation
//!         // side effects that should only be done once.
//!         acc.set(v);
//!         // drop `_guard` implicitly at end of scope
//!    }
//! }
//! ```

use crate::offchain::storage::StorageValueRef;
use codec::{Codec, Decode, Encode};
use sp_core::offchain::{Duration, Timestamp};
use sp_io::offchain;


/// Default expiry duration in milliseconds.
const STORAGE_LOCK_DEFAULT_EXPIRY_DURATION_MS: u64 = 30_000;

/// Snooze duration before attempting to lock again in ms.
const STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE: u64 = 100;

/// Lockable item for use with a persisted storage lock.
///
/// Bound for an item that has a stateful ordered meaning
/// without explicitly requiring `Ord` trait in general.
pub trait Lockable: Sized + Codec + Clone {
	/// Get the current value of lockable.
	fn current() -> Self;

	/// Acquire a new deadline based on `Self::current()`.
	fn deadline() -> Self;

	/// Verify the current value of `self` against `deadline`.
	/// to determine if the lock has expired.
	fn expired(&self, deadline: &Self) -> bool;

	/// Snooze the thread for time determined by `self` and `other`.
	///
	/// Only called if not expired just yet.
	/// Note that the deadline is only passed to allow some optimizations
	/// for some `L` types.
	fn snooze(&self, _deadline: &Self) {
		sp_io::offchain::sleep_until(offchain::timestamp().add(Duration::from_millis(
			STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE,
		)));
	}
}

impl Lockable for Timestamp {
	fn current() -> Self {
		offchain::timestamp()
	}

	fn deadline() -> Self {
		Self::current().add(Duration::from_millis(
			STORAGE_LOCK_DEFAULT_EXPIRY_DURATION_MS,
		))
	}

	fn expired(&self, reference: &Self) -> bool {
		<Self as Lockable>::current() > *reference
	}

	fn snooze(&self, deadline: &Self) {
		let remainder: Duration = self.diff(&deadline);
		// do not snooze the full duration, but instead snooze max 100ms
		// it might get unlocked in another thread
		// consider adding some additive jitter here
		let snooze = core::cmp::min(remainder.millis(), STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE);
		sp_io::offchain::sleep_until(self.add(Duration::from_millis(snooze)));
	}
}

/// Lockable based on the current block number and a timestamp based deadline.
#[derive(Encode, Decode)]
pub struct BlockAndTime<B: BlockNumberProvider> {
	/// The block number that has to be reached in order
	/// for the lock to be considered stale.
	pub block_number: <B as BlockNumberProvider>::BlockNumber,
	/// Additional timestamp based deadline which has to be
	/// reached in order for the lock to become stale.
	pub timestamp: Timestamp,
}

// derive not possible, since `B` does not necessarily implement `trait Clone`
impl<B: BlockNumberProvider> Clone for BlockAndTime<B> {
	fn clone(&self) -> Self {
		Self {
			block_number: self.block_number.clone(),
			timestamp: self.timestamp,
		}
	}
}


impl<B: BlockNumberProvider> Lockable for BlockAndTime<B>
{
	fn current() -> Self {
		Self {
			block_number: B::current_block_number(),
			timestamp: offchain::timestamp(),
		}
	}

	fn deadline() -> Self {
		Self {
			block_number: B::deadline_block_number(),
			timestamp: offchain::timestamp().add(Duration::from_millis(
				STORAGE_LOCK_DEFAULT_EXPIRY_DURATION_MS,
			)),
		}
	}

	fn expired(&self, reference: &Self) -> bool {
		let current = <Self as Lockable>::current();
		current.timestamp > reference.timestamp && current.block_number > reference.block_number
	}

	fn snooze(&self, deadline: &Self) {
		let remainder: Duration = self.timestamp.diff(&(deadline.timestamp));
		let snooze = core::cmp::min(remainder.millis(), STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE);
		sp_io::offchain::sleep_until(self.timestamp.add(Duration::from_millis(snooze)));
	}
}

/// Storage based lock.
///
/// A lock that is persisted in the DB and provides a mutex behavior
/// with a defined safety expiry deadline based on a [`Lockable`](Self::Lockable)
/// implementation.
pub struct StorageLock<'a, L> {
	// A storage value ref which defines the DB entry representing the lock.
	value_ref: StorageValueRef<'a>,
	deadline: L,
}

impl<'a, L> StorageLock<'a, L>
where
	L: Lockable,
{
	/// Create a new storage lock with [default expiry duration](Self::STORAGE_LOCK_DEFAULT_EXPIRY_DURATION_MS).
	pub fn new(key: &'a [u8]) -> Self {
		Self {
			value_ref: StorageValueRef::<'a>::persistent(key),
			deadline: L::deadline(),
		}
	}

	fn try_lock_inner(&mut self, new_deadline: L) -> Result<(), Option<L>> {
		let now = L::current();
		let res = self
			.value_ref
			.mutate(|s: Option<Option<L>>| -> Result<L, Option<L>> {
				match s {
					// no lock set, we can safely acquire it
					None => Ok(new_deadline),
					// lock is set, but it's old. We can re-acquire it.
					Some(Some(deadline)) if now.expired(&deadline) => Ok(new_deadline),
					// lock is present and is still active
					Some(Some(deadline)) => Err(Some(deadline)),
					_ => Err(None),
				}
			});
		match res {
			Ok(Ok(_)) => Ok(()),
			Ok(Err(_deadline)) => Err(None),
			Err(e) => Err(e),
		}
	}

	/// Attempt to lock the storage entry.
	///
	/// Returns a lock guard on success, otherwise an error containing `None` in
	/// case the mutex was already unlocked before, or if the lock is still held
	/// by another process `Err(Some(expiration_timestamp))`.
	pub fn try_lock<'b>(&'b mut self) -> Result<StorageLockGuard<'a, 'b, L>, Option<L>>
	where
		'a: 'b,
	{
	let _ = self.try_lock_inner(self.deadline.clone())?;
	Ok(StorageLockGuard::<'a, 'b> { lock: Some(self) })
	}

	/// Try grabbing the lock until its expiry is reached.
	///
	/// Returns an error if the lock expired before it could be caught.
	pub fn spin_lock(&mut self) -> StorageLockGuard<'a, '_, L>
	{
		loop {
			// blind attempt on locking
			let deadline = match self.try_lock_inner(self.deadline.clone()) {
				Ok(_) => return StorageLockGuard::<'a, '_, L> { lock: Some(self) },
				Err(Some(other_locks_deadline)) => other_locks_deadline,
				_ => L::deadline(), // use the default
			};
			L::current().snooze(&deadline);
		}
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
	/// Consume the guard but DO NOT unlock the underlying lock.
	pub fn forget(mut self) {
		let _ = self.lock.take();
	}
}

impl<'a, 'b, L: Lockable> Drop for StorageLockGuard<'a, 'b, L>
{
	fn drop(&mut self) {
		if let Some(lock) = self.lock.take() {
			lock.unlock();
		}
	}
}

/// Extension trait for locks based on [`Timestamp`](::sp_core::offchain::Timestamp).
///
/// Allows explicitly setting the timeout on construction
/// instead of using the implicit default timeout of
/// [`STORAGE_LOCK_DEFAULT_EXPIRY_DURATION_MS`](Self::STORAGE_LOCK_DEFAULT_EXPIRY_DURATION_MS).
pub trait TimeLock<'a>: Sized {
	/// Provide an explicit deadline timestamp at which the locked state of the lock
	/// becomes stale and may be dismissed by `fn try_lock(..)`, `fn spin_lock(..)` and others.
	fn with_deadline(key: &'a [u8], lock_deadline: Timestamp) -> Self;
}

impl<'a> TimeLock<'a> for StorageLock<'a, Timestamp> {
	fn with_deadline(key: &'a [u8], lock_deadline: Timestamp) -> Self {
		Self {
			value_ref: StorageValueRef::<'a>::persistent(key),
			deadline: lock_deadline,
		}
	}
}

/// Extension for storage locks which are based on blocks in addition to a timestamp.
///
/// The provider `B` does provide means of obtaining a default deadline as well as obtaining
/// the current block number. Expiry and others are actually checked.
trait BlockAndTimeLock<'a, B>: Sized
where
	B: BlockNumberProvider,
{
	fn with_block_and_time_deadline(
		key: &'a [u8],
		block_deadline: B::BlockNumber,
		time_deadline: Timestamp,
	) -> Self;
}

impl<'a, B> BlockAndTimeLock<'a, B> for StorageLock<'a, BlockAndTime<B>>
where
	B: BlockNumberProvider,
{
	fn with_block_and_time_deadline(
		key: &'a [u8],
		block_deadline: B::BlockNumber,
		time_deadline: Timestamp,
	) -> Self {
		Self {
			value_ref: StorageValueRef::<'a>::persistent(key),
			deadline: BlockAndTime {
				block_number: block_deadline,
				timestamp: time_deadline,
			},
		}
	}
}

/// Bound for block numbers which commonly will be implemented by the `frame_system::Trait::BlockNumber`.
///
/// This trait has no intrinsic meaning and exists only to decouple `frame_system`
/// from `runtime` crate and avoid a circular dependency.
pub trait BlockNumberProvider {
	/// Type of `BlockNumber` the provider is going to provide
	/// with `deadline()` and `current()`.
	type BlockNumber: Codec + Clone + Ord + Eq;
	/// Returns the current block number.
	///
	/// Commonly this will be implemented as
	/// ```ignore
	/// fn current() -> Self {
	///     frame_system::Module<Trait>::block_number()
	/// }
	/// ```
	/// but note that the definition of current is
	/// application specific.
	fn current_block_number() -> Self::BlockNumber;

	/// Provide a default deadline as `BlockNumber`.
	fn deadline_block_number() -> Self::BlockNumber;
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::offchain::{testing, OffchainExt, OffchainStorage};
	use sp_io::TestExternalities;

	const VAL_1: u32 = 0u32;
	const VAL_2: u32 = 0xFFFF_FFFFu32;

	#[test]
	fn storage_lock_write_unlock_lock_read_unlock() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainExt::new(offchain));

		t.execute_with(|| {
			let mut lock = StorageLock::<'_, Timestamp>::new(b"lock_1");

			let val = StorageValueRef::persistent(b"protected_value");

			{
				let _guard = lock.spin_lock();

				val.set(&VAL_1);

				assert_eq!(val.get::<u32>(), Some(Some(VAL_1)));
			}

			{
				let _guard = lock.spin_lock();
				val.set(&VAL_2);

				assert_eq!(val.get::<u32>(), Some(Some(VAL_2)));
			}
		});
		// lock must have been cleared at this point
		assert_eq!(state.read().persistent_storage.get(b"", b"lock_1"), None);
	}

	#[test]
	fn storage_lock_and_forget() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainExt::new(offchain));

		t.execute_with(|| {
			let mut lock = StorageLock::<'_, Timestamp>::new(b"lock_2");

			let val = StorageValueRef::persistent(b"protected_value");

			let guard = lock.spin_lock();

			val.set(&VAL_1);

			assert_eq!(val.get::<u32>(), Some(Some(VAL_1)));

			guard.forget();
		});
		// lock must have been cleared at this point
		let opt = state.read().persistent_storage.get(b"", b"lock_2");
		assert!(opt.is_some());
	}

	#[test]
	fn storage_lock_and_let_expire_and_lock_again() {
		let (offchain, state) = testing::TestOffchainExt::new();
		let mut t = TestExternalities::default();
		t.register_extension(OffchainExt::new(offchain));

		t.execute_with(|| {
			let sleep_until = Timestamp::current().add(Duration::from_millis(500));
			let lock_expiration = Timestamp::current().add(Duration::from_millis(200));

			let mut lock = StorageLock::<'_, Timestamp>::with_deadline(b"lock_3", lock_expiration);

			{
				let guard = lock.spin_lock();
				guard.forget();
			}

			// assure the lock expires
			offchain::sleep_until(sleep_until);

			let mut lock = StorageLock::<'_, Timestamp>::new(b"lock_3");
			let res = lock.try_lock();
			assert!(res.is_ok());
			let guard = res.unwrap();
			guard.forget();
		});

		// lock must have been cleared at this point
		let opt = state.read().persistent_storage.get(b"", b"lock_3");
		assert!(opt.is_some());
	}
}
