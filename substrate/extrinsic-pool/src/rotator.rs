// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Rotate extrinsic inside the pool.
//!
//! Keeps only recent extrinsic and discard the ones kept for a significant amount of time.
//! Discarded extrinsics are banned so that they don't get re-imported again.

use std::{
	collections::HashMap,
	fmt,
	hash,
	time::{Duration, Instant},
};
use parking_lot::RwLock;
use txpool::VerifiedTransaction;
use Verified;

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
		PoolRotator {
			ban_time: Duration::from_secs(60 * 30),
			banned_until: Default::default(),
		}
	}
}

impl<Hash: hash::Hash + Eq + Clone> PoolRotator<Hash> {
	/// Returns `true` if extrinsic hash is currently banned.
	pub fn is_banned(&self, hash: &Hash) -> bool {
		self.banned_until.read().contains_key(hash)
	}

	/// Bans extrinsic if it's stale.
	///
	/// Returns `true` if extrinsic is stale and got banned.
	pub fn ban_if_stale<Ex, VEx>(&self, now: &Instant, xt: &Verified<Ex, VEx>) -> bool where
		VEx: VerifiedTransaction<Hash=Hash>,
		Hash: fmt::Debug + fmt::LowerHex,
	{
		if &xt.valid_till > now {
			return false;
		}

		let mut banned = self.banned_until.write();
		banned.insert(xt.verified.hash().clone(), *now + self.ban_time);

		if banned.len() > 2 * EXPECTED_SIZE {
			while banned.len() > EXPECTED_SIZE {
				if let Some(key) = banned.keys().next().cloned() {
					banned.remove(&key);
				}
			}
		}

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
	use pool::tests::VerifiedTransaction;
	use test_client::runtime::Hash;

	fn rotator() -> PoolRotator<Hash> {
		PoolRotator {
			ban_time: Duration::from_millis(10),
			..Default::default()
		}
	}

	fn tx() -> (Hash, Verified<u64, VerifiedTransaction>) {
		let hash = 5.into();
		let tx = Verified {
			original: 5,
			verified: VerifiedTransaction {
				hash,
				sender: Default::default(),
				nonce: Default::default(),
			},
			valid_till: Instant::now(),
		};

		(hash, tx)
	}

	#[test]
	fn should_not_ban_if_not_stale() {
		// given
		let (hash, tx) = tx();
		let rotator = rotator();
		assert!(!rotator.is_banned(&hash));
		let past = Instant::now() - Duration::from_millis(1000);

		// when
		assert!(!rotator.ban_if_stale(&past, &tx));

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
		assert!(rotator.ban_if_stale(&Instant::now(), &tx));

		// then
		assert!(rotator.is_banned(&hash));
	}


	#[test]
	fn should_clear_banned() {
		// given
		let (hash, tx) = tx();
		let rotator = rotator();
		assert!(rotator.ban_if_stale(&Instant::now(), &tx));
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
		fn tx_with(i: u64, time: Instant) -> Verified<u64, VerifiedTransaction> {
			let hash = i.into();
			Verified {
				original: i,
				verified: VerifiedTransaction {
					hash,
					sender: Default::default(),
					nonce: Default::default(),
				},
				valid_till: time,
			}
		}

		let rotator = rotator();

		let now = Instant::now();
		let past = now - Duration::from_secs(1);

		// when
		for i in 0..2*EXPECTED_SIZE {
			let tx = tx_with(i as u64, past);
			assert!(rotator.ban_if_stale(&now, &tx));
		}
		assert_eq!(rotator.banned_until.read().len(), 2*EXPECTED_SIZE);

		// then
		let tx = tx_with(2*EXPECTED_SIZE as u64, past);
		// trigger a garbage collection
		assert!(rotator.ban_if_stale(&now, &tx));
		assert_eq!(rotator.banned_until.read().len(), EXPECTED_SIZE);
	}
}
