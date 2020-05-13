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
//! A persistent storage lock with a defined expire time.
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
//!         // modify `v` as desired
//!         acc.set(v);
//!    } else {
//!         // the lock duration expired
//!    }
//! }
//! ```

use crate::offchain::storage::StorageValueRef;
use sp_core::offchain::{Duration, Timestamp};
use sp_io::offchain;

/// Default expirey duration in milliseconds.
const STORAGE_LOCK_DEFAULT_EXPIREY_DURATION: u64 = 30_000;

/// Snooze duration before attempting to lock again in ms.
const STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE: u64 = 100;

/// A persisted guard state.
///
/// An in DB persistent mutex for multi access items which are modified
/// i.e. vecs or sets.
pub struct StorageLock<'a> {
	// A storage value ref which defines the DB entry representing the lock.
	value_ref: StorageValueRef<'a>,
	// `None` implies it was already released by `fn unlock(..)`
	locked_until: Option<Timestamp>,
}

impl<'a> StorageLock<'a> {
	/// Create a new storage lock with [default expirey duration](Self::STORAGE_LOCK_DEFAULT_EXPIREY_DURATION).
	pub fn new<'k>(key: &'k [u8]) -> Self
	where
		'k: 'a,
	{
		Self {
			value_ref: StorageValueRef::<'a>::persistent(key),
			locked_until: None,
		}
	}

	#[inline]
	fn try_lock_inner(&mut self, duration: Duration) -> Result<(), Option<Timestamp>> {
		let now = offchain::timestamp();
		let expires_at = now.add(duration);
		let res = self.value_ref.mutate(
			|s: Option<Option<Timestamp>>| -> Result<Timestamp, Option<Timestamp>> {
				match s {
					// no lock set, we can safely acquire it
					None => Ok(expires_at),
					// lock is set, but it's old. We can re-acquire it.
					Some(Some(current_good_until)) if current_good_until < now => Ok(expires_at),
					// lock is present and is still active
					Some(Some(current_good_until)) => Err(Some(current_good_until)),
					_ => Err(None),
				}
			},
		);
		match res {
			Ok(Ok(_)) => {
				self.locked_until = Some(expires_at);
				Ok(())
			}
			Ok(Err(timestamp)) => Err(Some(timestamp)), // failed to set the new value, but could read the current
			Err(e) => Err(e),                           // forward the remaining value
		}
	}

	/// Attempt to lock the storage entry.
	///
	/// Returns a lock guard on success, otherwise an error containing `None` in
	/// case the mutex was already unlocked before, or if the lock is still held
	/// by another process `Err(Some(expiration_timestamp))`.
	pub fn try_lock<'b>(&'b mut self) -> Result<StorageLockGuard<'a, 'b>, Option<Timestamp>>
	where
		'a: 'b,
	{
		if self.locked_until.is_none() {
			match self.try_lock_inner(Duration::from_millis(STORAGE_LOCK_DEFAULT_EXPIREY_DURATION))
			{
				Ok(_) => Ok(StorageLockGuard::<'a, 'b> { lock: Some(self) }),
				Err(e) => Err(e),
			}
		} else {
			Err(self.locked_until)
		}
	}

	/// Try grabbing the lock until its expiry is reached.
	///
	/// Returns an error if the lock expired before it could be cought
	pub fn spin_lock<'b, 'c>(&'b mut self) -> Result<StorageLockGuard<'a, 'c>, ()>
	where
		'a: 'b,
		'b: 'c,
	{
		if self.locked_until.is_none() {
			loop {
				// blind attempt on locking
				let expires_at = match self
					.try_lock_inner(Duration::from_millis(STORAGE_LOCK_DEFAULT_EXPIREY_DURATION))
				{
					Ok(_) => return Ok(StorageLockGuard::<'a, 'b> { lock: Some(self) }),
					Err(None) => return Err(()),
					Err(Some(expires_at)) => expires_at,
				};
				let remainder: Duration = offchain::timestamp().diff(&expires_at);
				// do not snooze the full duration, but instead snooze max 100ms
				// it might get unlocked in another thread
				// consider adding some additive jitter here
				let snooze =
					core::cmp::min(remainder.millis(), STORAGE_LOCK_PER_CHECK_ITERATION_SNOOZE);
				sp_io::offchain::sleep_until(
					offchain::timestamp().add(Duration::from_millis(snooze)),
				);
			}
		} else {
			Err(())
		}
	}

	/// Explicitly unlock the lock.
	///
	/// Does nothing if the lock was alrady unlocked before.
	pub fn unlock(&mut self) {
		if let Some(_) = self.locked_until.take() {
			self.value_ref.remove();
		}
	}
}

/// RAII style guard for a lock.
pub struct StorageLockGuard<'a, 'b> {
	lock: Option<&'b mut StorageLock<'a>>,
}

impl<'a, 'b> StorageLockGuard<'a, 'b> {
	/// Consume the guard and unlock the underlying lock.
	pub fn forget(mut self) {
		let _ = self.lock.take();
	}
}

impl<'a, 'b> Drop for StorageLockGuard<'a, 'b> {
	fn drop(&mut self) {
		if let Some(lock) = self.lock.take() {
			lock.unlock();
		}
	}
}
