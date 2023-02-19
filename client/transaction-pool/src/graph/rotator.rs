// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Rotate extrinsic inside the pool.
//!
//! Keeps only recent extrinsic and discard the ones kept for a significant amount of time.
//! Discarded extrinsics are banned so that they don't get re-imported again.

use parking_lot::RwLock;
use std::{
	collections::HashMap,
	hash, iter,
	time::{Duration, Instant},
};

use super::base_pool::Transaction;

/// Expected size of the banned extrinsics cache.
const EXPECTED_SIZE: usize = 2048;

/// Pool rotator is responsible to only keep fresh extrinsics in the pool.
///
/// Extrinsics that occupy the pool for too long are culled and temporarily banned from entering
/// the pool again.
pub struct PoolRotator<Hash> {
	/// How long the extrinsic is banned for.
	ban_time: Duration,
	/// Currently banned extrinsics.
	banned_until: RwLock<HashMap<Hash, Instant>>,
}

impl<Hash: hash::Hash + Eq> Default for PoolRotator<Hash> {
	fn default() -> Self {
		Self { ban_time: Duration::from_secs(60 * 30), banned_until: Default::default() }
	}
}

impl<Hash: hash::Hash + Eq + Clone> PoolRotator<Hash> {
	/// New rotator instance with specified ban time.
	pub fn new(ban_time: Duration) -> Self {
		Self { ban_time, banned_until: Default::default() }
	}

	/// Returns `true` if extrinsic hash is currently banned.
	pub fn is_banned(&self, hash: &Hash) -> bool {
		self.banned_until.read().contains_key(hash)
	}

	/// Bans given set of hashes.
	pub fn ban(&self, now: &Instant, hashes: impl IntoIterator<Item = Hash>) {
		let mut banned = self.banned_until.write();

		for hash in hashes {
			banned.insert(hash, *now + self.ban_time);
		}

		if banned.len() > 2 * EXPECTED_SIZE {
			while banned.len() > EXPECTED_SIZE {
				if let Some(key) = banned.keys().next().cloned() {
					banned.remove(&key);
				}
			}
		}
	}

	/// Bans extrinsic if it's stale.
	///
	/// Returns `true` if extrinsic is stale and got banned.
	pub fn ban_if_stale<Ex>(
		&self,
		now: &Instant,
		current_block: u64,
		xt: &Transaction<Hash, Ex>,
	) -> bool {
		if xt.valid_till > current_block {
			return false
		}

		self.ban(now, iter::once(xt.hash.clone()));
		true
	}

	/// Removes timed bans.
	pub fn clear_timeouts(&self, now: &Instant) {
		let mut banned = self.banned_until.write();

		banned.retain(|_, &mut v| v >= *now);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::transaction_validity::TransactionSource;

	type Hash = u64;
	type Ex = ();

	fn rotator() -> PoolRotator<Hash> {
		PoolRotator { ban_time: Duration::from_millis(10), ..Default::default() }
	}

	fn tx() -> (Hash, Transaction<Hash, Ex>) {
		let hash = 5u64;
		let tx = Transaction {
			data: (),
			bytes: 1,
			hash,
			priority: 5,
			valid_till: 1,
			requires: vec![],
			provides: vec![],
			propagate: true,
			source: TransactionSource::External,
		};

		(hash, tx)
	}

	#[test]
	fn should_not_ban_if_not_stale() {
		// given
		let (hash, tx) = tx();
		let rotator = rotator();
		assert!(!rotator.is_banned(&hash));
		let now = Instant::now();
		let past_block = 0;

		// when
		assert!(!rotator.ban_if_stale(&now, past_block, &tx));

		// then
		assert!(!rotator.is_banned(&hash));
	}

	#[test]
	fn should_ban_stale_extrinsic() {
		// given
		let (hash, tx) = tx();
		let rotator = rotator();
		assert!(!rotator.is_banned(&hash));

		// when
		assert!(rotator.ban_if_stale(&Instant::now(), 1, &tx));

		// then
		assert!(rotator.is_banned(&hash));
	}

	#[test]
	fn should_clear_banned() {
		// given
		let (hash, tx) = tx();
		let rotator = rotator();
		assert!(rotator.ban_if_stale(&Instant::now(), 1, &tx));
		assert!(rotator.is_banned(&hash));

		// when
		let future = Instant::now() + rotator.ban_time + rotator.ban_time;
		rotator.clear_timeouts(&future);

		// then
		assert!(!rotator.is_banned(&hash));
	}

	#[test]
	fn should_garbage_collect() {
		// given
		fn tx_with(i: u64, valid_till: u64) -> Transaction<Hash, Ex> {
			let hash = i;
			Transaction {
				data: (),
				bytes: 2,
				hash,
				priority: 5,
				valid_till,
				requires: vec![],
				provides: vec![],
				propagate: true,
				source: TransactionSource::External,
			}
		}

		let rotator = rotator();

		let now = Instant::now();
		let past_block = 0;

		// when
		for i in 0..2 * EXPECTED_SIZE {
			let tx = tx_with(i as u64, past_block);
			assert!(rotator.ban_if_stale(&now, past_block, &tx));
		}
		assert_eq!(rotator.banned_until.read().len(), 2 * EXPECTED_SIZE);

		// then
		let tx = tx_with(2 * EXPECTED_SIZE as u64, past_block);
		// trigger a garbage collection
		assert!(rotator.ban_if_stale(&now, past_block, &tx));
		assert_eq!(rotator.banned_until.read().len(), EXPECTED_SIZE);
	}
}
