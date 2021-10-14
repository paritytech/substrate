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

use chrono::{Datelike, Timelike};
use std::{cell::RefCell, fmt::Write, time::SystemTime};
use tracing_subscriber::fmt::time::FormatTime;

/// A structure which, when `Display`d, will print out the current local time.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Default)]
pub struct FastLocalTime {
	/// Decides whenever the fractional timestamp with be included in the output.
	///
	/// If `false` the output will match the following `chrono` format string:
	///   `%Y-%m-%d %H:%M:%S`
	///
	/// If `true` the output will match the following `chrono` format string:
	///   `%Y-%m-%d %H:%M:%S%.3f`
	pub with_fractional: bool,
}

// This is deliberately slightly larger than we actually need, just in case.
const TIMESTAMP_MAXIMUM_LENGTH: usize = 32;

#[derive(Default)]
struct InlineString {
	buffer: [u8; TIMESTAMP_MAXIMUM_LENGTH],
	length: usize,
}

impl Write for InlineString {
	fn write_str(&mut self, s: &str) -> std::fmt::Result {
		let new_length = self.length + s.len();
		assert!(
			new_length <= TIMESTAMP_MAXIMUM_LENGTH,
			"buffer overflow when formatting the current timestamp"
		);

		self.buffer[self.length..new_length].copy_from_slice(s.as_bytes());
		self.length = new_length;
		Ok(())
	}
}

impl InlineString {
	fn as_str(&self) -> &str {
		// SAFETY: this is safe since the only place we append to the buffer
		//         is in `write_str` from an `&str`
		unsafe { std::str::from_utf8_unchecked(&self.buffer[..self.length]) }
	}
}

#[derive(Default)]
struct CachedTimestamp {
	buffer: InlineString,
	last_regenerated_at: u64,
	last_fractional: u32,
}

thread_local! {
	static TIMESTAMP: RefCell<CachedTimestamp> = Default::default();
}

impl FormatTime for FastLocalTime {
	fn format_time(&self, w: &mut dyn Write) -> std::fmt::Result {
		const TIMESTAMP_PARTIAL_LENGTH: usize = "0000-00-00 00:00:00".len();

		let elapsed = SystemTime::now()
			.duration_since(SystemTime::UNIX_EPOCH)
			.expect("system time is never before UNIX epoch; qed");
		let unix_time = elapsed.as_secs();

		TIMESTAMP.with(|cache| {
			let mut cache = cache.borrow_mut();

			// Regenerate the timestamp only at most once each second.
			if cache.last_regenerated_at != unix_time {
				let ts = chrono::Local::now();
				let fractional = (ts.nanosecond() % 1_000_000_000) / 1_000_000;
				cache.last_regenerated_at = unix_time;
				cache.last_fractional = fractional;
				cache.buffer.length = 0;

				write!(
					&mut cache.buffer,
					"{:04}-{:02}-{:02} {:02}:{:02}:{:02}.{:03}",
					ts.year(),
					ts.month(),
					ts.day(),
					ts.hour(),
					ts.minute(),
					ts.second(),
					fractional
				)?;
			} else if self.with_fractional {
				let fractional = elapsed.subsec_millis();

				// Regenerate the fractional part at most once each millisecond.
				if cache.last_fractional != fractional {
					cache.last_fractional = fractional;
					cache.buffer.length = TIMESTAMP_PARTIAL_LENGTH + 1;
					write!(&mut cache.buffer, "{:03}", fractional)?;
				}
			}

			let mut slice = cache.buffer.as_str();
			if !self.with_fractional {
				slice = &slice[..TIMESTAMP_PARTIAL_LENGTH];
			}

			w.write_str(slice)
		})
	}
}

impl std::fmt::Display for FastLocalTime {
	fn fmt(&self, w: &mut std::fmt::Formatter) -> std::fmt::Result {
		self.format_time(w)
	}
}

#[test]
fn test_format_fast_local_time() {
	assert_eq!(
		chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string().len(),
		FastLocalTime { with_fractional: false }.to_string().len()
	);
	assert_eq!(
		chrono::Local::now().format("%Y-%m-%d %H:%M:%S%.3f").to_string().len(),
		FastLocalTime { with_fractional: true }.to_string().len()
	);

	// A simple trick to make sure this test won't randomly fail if we so happen
	// to land on the exact moment when we tick over to the next second.
	let now_1 = FastLocalTime { with_fractional: false }.to_string();
	let expected = chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string();
	let now_2 = FastLocalTime { with_fractional: false }.to_string();

	assert!(
		now_1 == expected || now_2 == expected,
		"'{}' or '{}' should have been equal to '{}'",
		now_1,
		now_2,
		expected
	);
}
