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
//! The lock is using Local Storage and allows synchronizing
//! access to critical section of your code for concurrently running Off-chain Workers.
//! Usage of `PERSISTENT` variant of the storage persists the lock value even in case of re-orgs.
//!
//! A use case for the lock is to make sure that a particular section of the code is only run
//! by one Off-chain Worker at the time. This may include performing a side-effect (i.e. an HTTP call)
//! or alteration of single or multiple Local Storage entries.
//!
//! One use case would be collective updates of multiple data items
//! or append / remove of i.e. sets, vectors which are stored in
//! the offchain storage DB.
//!
//! ## Example:
//!
//! ```rust
//! // in your off-chain worker code
//!
//! fn append_to_in_storage_vec<'k, T>(key: &'k [u8], T) where T: Encode {
//!    let mut lock = StorageLock::new(b"x::lock");
//!    if let Ok(_guard) =  lock.spin_lock() {
//!         let acc = StorageValueRef::persistent(key);
//!         let v: Vec<T> = acc.get::<Vec<T>>().unwrap().unwrap();
//!         // modify `v` as desired - i.e. perform some heavy computation or side effects that should only be done once.
//!         acc.set(v);
//!    } else {
//!         // the lock duration expired
//!    }
//! }
//! ```

use crate::offchain::storage::StorageValueRef;
use codec::Codec;
use sp_core::offchain::{Duration, Timestamp};
use sp_io::offchain;

//use frame_system how?

/// Default expiry duration in milliseconds.
const STORAGE_LOCK_DEFAULT_EXPIRY_DURATION_MS: u64 = 30_000;

/// Snooze duration before attempting to lock again in ms.
const STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE: u64 = 100;

pub trait Lockable: Sized + Codec + Copy {
    /// Get the current value of lockable.
    fn current() -> Self;

    /// Acquire a new deadline based on `Self::current()`
    fn deadline() -> Self;

    /// Verify the current value of `self` and `other`
    /// to determine if the lock has expired.
    fn expired(&self, other: &Self) -> bool;

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
        Self::current().add(Duration::from_millis(STORAGE_LOCK_DEFAULT_EXPIRY_DURATION_MS))
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

/// A persisted guard state.
///
/// An in DB persistent mutex for multi access items which are modified
/// i.e. vecs or sets.
pub struct StorageLock<'a, L>
where
    L: Sized + Lockable,
{
    // A storage value ref which defines the DB entry representing the lock.
    value_ref: StorageValueRef<'a>,
    deadline: L,
}

impl<'a, L> StorageLock<'a, L>
where
    L: Lockable,
{
	/// Create a new storage lock with [default expiry duration](Self::STORAGE_LOCK_DEFAULT_EXPIRY_DURATION_MS).
    pub fn new<'k>(key: &'k [u8]) -> Self
    where
        'k: 'a,
    {
        Self {
            value_ref: StorageValueRef::<'a>::persistent(key),
            deadline: L::deadline(),
        }
    }

    #[inline]
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
        match self.try_lock_inner(self.deadline) {
            Ok(_) => Ok(StorageLockGuard::<'a, 'b> { lock: Some(self) }),
            Err(e) => Err(e),
        }
    }

	/// Try grabbing the lock until its expiry is reached.
	///
	/// Returns an error if the lock expired before it could be caught.
    pub fn spin_lock<'b, 'c>(&'b mut self) -> StorageLockGuard<'a, 'b, L>
    where
        'a: 'b,
    {
        loop {
            // blind attempt on locking
            let deadline = match self.try_lock_inner(self.deadline) {
                Ok(_) => return StorageLockGuard::<'a, 'b, L> { lock: Some(self) },
                Err(Some(other_locks_deadline)) => other_locks_deadline,
                _ => L::deadline(), // use the default
            };
            L::current().snooze(&deadline);
        }
    }

	/// Explicitly unlock the lock.
    pub fn unlock(&mut self) {
        self.value_ref.clear();
    }
}

pub trait TimeLock<'a>: Sized {
    fn with_deadline<'k>(key: &'k [u8], lock_deadline: Timestamp) -> Self
    where
        'k: 'a;
}

impl<'a> TimeLock<'a> for StorageLock<'a, Timestamp> {
    fn with_deadline<'k>(key: &'k [u8], lock_deadline: Timestamp) -> Self
    where
        'k: 'a,
    {
        Self {
            value_ref: StorageValueRef::<'a>::persistent(key),
            deadline: lock_deadline,
        }
    }
}

// trait BlockAndTimeLock<T>: Sized where T::BlockNumber: Codec, T: frame_system::Trait {
// 	fn with_blocks_and_deadline<'k>(key: &'k [u8], block_deadline: T::BlockNumber, time_deadline: Timestamp) -> Self;
// }

// impl<T: frame_system::Trait> BlockAndTimeLock<T> for StorageLock<BlockAndTime<T>>  where T::BlockNumber: Codec, T: frame_system::Trait {
// 	fn with_blocks_and_time_deadline<'k>(key: &'k [u8], block_deadline: T::BlockNumber, time_deadline: Timestamp) -> Self {
// 		unimplemented!()
// 	}
// }

/// RAII style guard for a lock.
pub struct StorageLockGuard<'a, 'b, L>
where
    L: Lockable,
{
    lock: Option<&'b mut StorageLock<'a, L>>,
}

impl<'a, 'b, L> StorageLockGuard<'a, 'b, L>
where
    L: Lockable,
{
    /// Consume the guard but DO NOT unlock the underlying lock.
    pub fn forget(mut self) {
        let _ = self.lock.take();
    }
}

impl<'a, 'b, L> Drop for StorageLockGuard<'a, 'b, L>
where
    L: Lockable,
{
    fn drop(&mut self) {
        if let Some(lock) = self.lock.take() {
            lock.unlock();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sp_core::offchain::{testing, OffchainExt, OffchainStorage};
    use sp_io::TestExternalities;

    #[test]
    fn simple_lock_write_unlock_lock_read_unlock() {
        let (offchain, state) = testing::TestOffchainExt::new();
        let mut t = TestExternalities::default();
        t.register_extension(OffchainExt::new(offchain));

        t.execute_with(|| {
            let val1 = 0u32;
            let val2 = 0xFFFF_FFFFu32;

            let mut lock = StorageLock::<'_, Timestamp>::new(b"lock");

            let val = StorageValueRef::persistent(b"protected_value");

            {
                let _guard = lock.spin_lock();

                val.set(&val1);

                assert_eq!(val.get::<u32>(), Some(Some(val1)));
            }

            {
                let _guard = lock.spin_lock();
                val.set(&val2);

                assert_eq!(val.get::<u32>(), Some(Some(val2)));
            }
        });
        // lock must have been cleared at this point
        assert_eq!(
            state.read().persistent_storage.get(b"Storage", b"lock"),
            None
        );
    }
}
