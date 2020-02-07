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

//! Helper methods dedicated to timestamps.

use sp_core::offchain::Timestamp;
use std::convert::TryInto;
use std::time::{SystemTime, Duration};

/// Returns the current time as a `Timestamp`.
pub fn now() -> Timestamp {
	let now = SystemTime::now();
	let epoch_duration = now.duration_since(SystemTime::UNIX_EPOCH);
	match epoch_duration {
		Err(_) => {
			// Current time is earlier than UNIX_EPOCH.
			Timestamp::from_unix_millis(0)
		},
		Ok(d) => {
			let duration = d.as_millis();
			// Assuming overflow won't happen for a few hundred years.
			Timestamp::from_unix_millis(duration.try_into()
				.expect("epoch milliseconds won't overflow u64 for hundreds of years; qed"))
		}
	}
}

/// Returns how a `Timestamp` compares to "now".
///
/// In other words, returns `timestamp - now()`.
pub fn timestamp_from_now(timestamp: Timestamp) -> Duration {
	Duration::from_millis(timestamp.diff(&now()).millis())
}

/// Converts the deadline into a `Future` that resolves when the deadline is reached.
///
/// If `None`, returns a never-ending `Future`.
pub fn deadline_to_future(
	deadline: Option<Timestamp>,
) -> futures::future::MaybeDone<impl futures::Future> {
	use futures::future;

	future::maybe_done(match deadline {
		Some(deadline) => future::Either::Left(
			futures_timer::Delay::new(timestamp_from_now(deadline))
		),
		None => future::Either::Right(future::pending())
	})
}
