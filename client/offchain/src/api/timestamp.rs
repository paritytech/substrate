// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Helper methods dedicated to timestamps.

use sp_core::offchain::Timestamp;
use std::{
	convert::TryInto,
	time::{Duration, SystemTime},
};

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
			Timestamp::from_unix_millis(
				duration
					.try_into()
					.expect("epoch milliseconds won't overflow u64 for hundreds of years; qed"),
			)
		},
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
) -> futures::future::MaybeDone<impl futures::Future<Output = ()>> {
	use futures::future::{self, Either};

	future::maybe_done(match deadline.map(timestamp_from_now) {
		None => Either::Left(future::pending()),
		// Only apply delay if we need to wait a non-zero duration
		Some(duration) if duration <= Duration::from_secs(0) =>
			Either::Right(Either::Left(future::ready(()))),
		Some(duration) => Either::Right(Either::Right(futures_timer::Delay::new(duration))),
	})
}
