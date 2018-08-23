// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Rotate extrinsic inside the pool.
//!
//! Keeps only recent extrinsic and discard the ones kept for a significant amount of time.
//! Discarded extrinsics are banned so that they don't get re-imported again.

use std::{
	collections::HashMap,
	time::{Duration, Instant},
};
use parking_lot::RwLock;
use primitives::Hash;
use VerifiedTransaction;

/// Pool rotator is responsible to only keep fresh extrinsics in the pool.
///
/// Extrinsics that occupy the pool for too long are culled and temporarily banned from entering
/// the pool again.
pub struct PoolRotator {
	/// How long the extrinsic is banned for.
	ban_time: Duration,
	/// Currently banned extrinsics.
	banned_until: RwLock<HashMap<Hash, Instant>>,
}

impl Default for PoolRotator {
	fn default() -> Self {
		PoolRotator {
			ban_time: Duration::from_secs(60 * 30),
			banned_until: Default::default(),
		}
	}
}

impl PoolRotator {
	/// Returns `true` if extrinsic hash is currently banned.
	pub fn is_banned(&self, hash: &Hash) -> bool {
		self.banned_until.read().contains_key(hash)
	}

	/// Bans extrinsic if it's stale.
	///
	/// Returns `true` if extrinsic is stale and got banned.
	pub fn ban_if_stale(&self, now: &Instant, tx: &VerifiedTransaction) -> bool {
		if &tx.valid_till > now {
			return false;
		}

		self.banned_until.write().insert(*tx.hash(), *now + self.ban_time);
		true
	}

	/// Removes timed bans.
	pub fn clear_timeouts(&self, now: &Instant) {
		let to_remove = {
			self.banned_until.read()
				.iter()
				.filter_map(|(k, v)| if v < now {
					Some(*k)
				} else {
					None
				}).collect::<Vec<_>>()
		};

		let mut banned = self.banned_until.write();
		for k in to_remove {
			banned.remove(&k);
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime::{Extrinsic, Call, TimestampCall, UncheckedExtrinsic};

	fn rotator() -> PoolRotator {
		PoolRotator {
			ban_time: Duration::from_millis(10),
			..Default::default()
		}
	}

	fn tx() -> (Hash, VerifiedTransaction) {
		let hash: Hash = 5.into();
		let tx = VerifiedTransaction {
			original: UncheckedExtrinsic::new(
				Extrinsic {
					function: Call::Timestamp(TimestampCall::set(100_000_000)),
					signed: Default::default(),
					index: Default::default(),
				},
				Default::default(),
			),
			inner: None,
			sender: None,
			hash: hash.clone(),
			encoded_size: 1024,
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
}
