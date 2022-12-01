// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Provides a generic wrapper around shared data. See [`SharedData`] for more information.

use parking_lot::{Condvar, MappedMutexGuard, Mutex, MutexGuard};
use std::sync::Arc;

/// Created by [`SharedDataLocked::release_mutex`].
///
/// As long as the object isn't dropped, the shared data is locked. It is advised to drop this
/// object when the shared data doesn't need to be locked anymore. To get access to the shared data
/// [`Self::upgrade`] is provided.
#[must_use = "Shared data will be unlocked on drop!"]
pub struct SharedDataLockedUpgradable<T> {
	shared_data: SharedData<T>,
}

impl<T> SharedDataLockedUpgradable<T> {
	/// Upgrade to a *real* mutex guard that will give access to the inner data.
	///
	/// Every call to this function will reaquire the mutex again.
	pub fn upgrade(&mut self) -> MappedMutexGuard<T> {
		MutexGuard::map(self.shared_data.inner.lock(), |i| &mut i.shared_data)
	}
}

impl<T> Drop for SharedDataLockedUpgradable<T> {
	fn drop(&mut self) {
		let mut inner = self.shared_data.inner.lock();
		// It should not be locked anymore
		inner.locked = false;

		// Notify all waiting threads.
		self.shared_data.cond_var.notify_all();
	}
}

/// Created by [`SharedData::shared_data_locked`].
///
/// As long as this object isn't dropped, the shared data is held in a mutex guard and the shared
/// data is tagged as locked. Access to the shared data is provided through
/// [`Deref`](std::ops::Deref) and [`DerefMut`](std::ops::DerefMut). The trick is to use
/// [`Self::release_mutex`] to release the mutex, but still keep the shared data locked. This means
/// every other thread trying to access the shared data in this time will need to wait until this
/// lock is freed.
///
/// If this object is dropped without calling [`Self::release_mutex`], the lock will be dropped
/// immediately.
#[must_use = "Shared data will be unlocked on drop!"]
pub struct SharedDataLocked<'a, T> {
	/// The current active mutex guard holding the inner data.
	inner: MutexGuard<'a, SharedDataInner<T>>,
	/// The [`SharedData`] instance that created this instance.
	///
	/// This instance is only taken on drop or when calling [`Self::release_mutex`].
	shared_data: Option<SharedData<T>>,
}

impl<'a, T> SharedDataLocked<'a, T> {
	/// Release the mutex, but keep the shared data locked.
	pub fn release_mutex(mut self) -> SharedDataLockedUpgradable<T> {
		SharedDataLockedUpgradable {
			shared_data: self.shared_data.take().expect("`shared_data` is only taken on drop; qed"),
		}
	}
}

impl<'a, T> Drop for SharedDataLocked<'a, T> {
	fn drop(&mut self) {
		if let Some(shared_data) = self.shared_data.take() {
			// If the `shared_data` is still set, it means [`Self::release_mutex`] wasn't
			// called and the lock should be released.
			self.inner.locked = false;

			// Notify all waiting threads about the released lock.
			shared_data.cond_var.notify_all();
		}
	}
}

impl<'a, T> std::ops::Deref for SharedDataLocked<'a, T> {
	type Target = T;

	fn deref(&self) -> &Self::Target {
		&self.inner.shared_data
	}
}

impl<'a, T> std::ops::DerefMut for SharedDataLocked<'a, T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.inner.shared_data
	}
}

/// Holds the shared data and if the shared data is currently locked.
///
/// For more information see [`SharedData`].
struct SharedDataInner<T> {
	/// The actual shared data that is protected here against concurrent access.
	shared_data: T,
	/// Is `shared_data` currently locked and can not be accessed?
	locked: bool,
}

/// Some shared data that provides support for locking this shared data for some time.
///
/// When working with consensus engines there is often data that needs to be shared between multiple
/// parts of the system, like block production and block import. This struct provides an abstraction
/// for this shared data in a generic way.
///
/// The pain point when sharing this data is often the usage of mutex guards in an async context as
/// this doesn't work for most of them as these guards don't implement `Send`. This abstraction
/// provides a way to lock the shared data, while not having the mutex locked. So, the data stays
/// locked and we are still able to hold this lock over an `await` call.
///
/// # Example
///
/// ```
/// # use sc_consensus::shared_data::SharedData;
///
/// let shared_data = SharedData::new(String::from("hello world"));
///
/// let lock = shared_data.shared_data_locked();
///
/// let shared_data2 = shared_data.clone();
/// let join_handle1 = std::thread::spawn(move || {
///     // This will need to wait for the outer lock to be released before it can access the data.
///     shared_data2.shared_data().push_str("1");
/// });
///
/// assert_eq!(*lock, "hello world");
///
/// // Let us release the mutex, but we still keep it locked.
/// // Now we could call `await` for example.
/// let mut lock = lock.release_mutex();
///
/// let shared_data2 = shared_data.clone();
/// let join_handle2 = std::thread::spawn(move || {
///     shared_data2.shared_data().push_str("2");
/// });
///
/// // We still have the lock and can upgrade it to access the data.
/// assert_eq!(*lock.upgrade(), "hello world");
/// lock.upgrade().push_str("3");
///
/// drop(lock);
/// join_handle1.join().unwrap();
/// join_handle2.join().unwrap();
///
/// let data = shared_data.shared_data();
/// // As we don't know the order of the threads, we need to check for both combinations
/// assert!(*data == "hello world321" || *data == "hello world312");
/// ```
pub struct SharedData<T> {
	inner: Arc<Mutex<SharedDataInner<T>>>,
	cond_var: Arc<Condvar>,
}

impl<T> Clone for SharedData<T> {
	fn clone(&self) -> Self {
		Self { inner: self.inner.clone(), cond_var: self.cond_var.clone() }
	}
}

impl<T> SharedData<T> {
	/// Create a new instance of [`SharedData`] to share the given `shared_data`.
	pub fn new(shared_data: T) -> Self {
		Self {
			inner: Arc::new(Mutex::new(SharedDataInner { shared_data, locked: false })),
			cond_var: Default::default(),
		}
	}

	/// Acquire access to the shared data.
	///
	/// This will give mutable access to the shared data. After the returned mutex guard is dropped,
	/// the shared data is accessible by other threads. So, this function should be used when
	/// reading/writing of the shared data in a local context is required.
	///
	/// When requiring to lock shared data for some longer time, even with temporarily releasing the
	/// lock, [`Self::shared_data_locked`] should be used.
	pub fn shared_data(&self) -> MappedMutexGuard<T> {
		let mut guard = self.inner.lock();

		while guard.locked {
			self.cond_var.wait(&mut guard);
		}

		debug_assert!(!guard.locked);

		MutexGuard::map(guard, |i| &mut i.shared_data)
	}

	/// Acquire access to the shared data and lock it.
	///
	/// This will give mutable access to the shared data. The returned [`SharedDataLocked`]
	/// provides the function [`SharedDataLocked::release_mutex`] to release the mutex, but
	/// keeping the data locked. This is useful in async contexts for example where the data needs
	/// to be locked, but a mutex guard can not be held.
	///
	/// For an example see [`SharedData`].
	pub fn shared_data_locked(&self) -> SharedDataLocked<T> {
		let mut guard = self.inner.lock();

		while guard.locked {
			self.cond_var.wait(&mut guard);
		}

		debug_assert!(!guard.locked);
		guard.locked = true;

		SharedDataLocked { inner: guard, shared_data: Some(self.clone()) }
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn shared_data_locking_works() {
		const THREADS: u32 = 100;
		let shared_data = SharedData::new(0u32);

		let lock = shared_data.shared_data_locked();

		for i in 0..THREADS {
			let data = shared_data.clone();
			std::thread::spawn(move || {
				if i % 2 == 1 {
					*data.shared_data() += 1;
				} else {
					let mut lock = data.shared_data_locked().release_mutex();
					// Give the other threads some time to wake up
					std::thread::sleep(std::time::Duration::from_millis(10));
					*lock.upgrade() += 1;
				}
			});
		}

		let lock = lock.release_mutex();
		std::thread::sleep(std::time::Duration::from_millis(100));
		drop(lock);

		while *shared_data.shared_data() < THREADS {
			std::thread::sleep(std::time::Duration::from_millis(100));
		}
	}
}
