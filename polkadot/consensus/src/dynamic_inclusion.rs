// Copyright 2017 Parity Technologies (UK) Ltd.
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
//! Dynamic inclusion threshold over time.

use std::time::{Duration, Instant};

fn duration_to_micros(duration: &Duration) -> u64 {
	duration.as_secs() * 1_000_000 + (duration.subsec_nanos() / 1000) as u64
}

/// Dynamic inclusion threshold over time.
///
/// The acceptable proportion of parachains which must have parachain candidates
/// reduces over time (eventually going to zero).
pub struct DynamicInclusion {
	start: Instant,
	y: i64,
	m: i64,
}

impl DynamicInclusion {
	/// Constructs a new dynamic inclusion threshold calculator based on the time now,
	/// how many parachain candidates are required at the beginning, and when an empty
	/// block will be allowed.
	pub fn new(initial: usize, start: Instant, allow_empty: Duration) -> Self {
		// linear function f(n_candidates) -> valid after milliseconds
		// f(0) = allow_empty
		// f(initial) = 0
		let y = duration_to_micros(&allow_empty) as i64;
		let m = -y / initial as i64;

		DynamicInclusion {
			start,
			y,
			m,
		}
	}

	/// Returns the duration from `now` after which the amount of included parachain candidates
	/// would be enough, or `None` if it is sufficient now.
	///
	/// Panics if `now` is earlier than the `start`.
	pub fn acceptable_in(&self, now: Instant, included: usize) -> Option<Duration> {
		let elapsed = now.duration_since(self.start);
		let elapsed_millis = duration_to_micros(&elapsed) as i64;

		let valid_after_millis = self.y + self.m * included as i64;

		if elapsed_millis >= valid_after_millis {
			None
		} else {
			Some(Duration::from_millis((valid_after_millis - elapsed_millis) as u64 / 1000))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn full_immediately_allowed() {
		let now = Instant::now();

		let dynamic = DynamicInclusion::new(
			10,
			now,
			Duration::from_millis(4000),
		);

		assert!(dynamic.acceptable_in(now, 10).is_none());
		assert!(dynamic.acceptable_in(now, 11).is_none());
		assert!(dynamic.acceptable_in(now + Duration::from_millis(2000), 10).is_none());
	}

	#[test]
	fn half_allowed_halfway() {
		let now = Instant::now();

		let dynamic = DynamicInclusion::new(
			10,
			now,
			Duration::from_millis(4000),
		);

		assert_eq!(dynamic.acceptable_in(now, 5), Some(Duration::from_millis(2000)));
		assert!(dynamic.acceptable_in(now + Duration::from_millis(2000), 5).is_none());
		assert!(dynamic.acceptable_in(now + Duration::from_millis(3000), 5).is_none());
		assert!(dynamic.acceptable_in(now + Duration::from_millis(4000), 5).is_none());
	}
}
