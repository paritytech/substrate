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

use chrono::{DateTime, Duration, format::ParseResult, TimeZone, Utc};

use parking_lot::Mutex;

use std::{fs, path::Path};

use tracing::{event::Event, Subscriber};
use tracing_subscriber::{
	layer::Context,
	registry::LookupSpan,
	Layer};

pub struct CleanLayer {
	/// tracing save days
	day: i64,
	/// Old expiration time
	old_expire_time: Mutex<DateTime<Utc>>,
	/// tracing storage directory
	dir: String,
	///	Datetime format string
	fmt: String,
}

impl CleanLayer
{
	/// Return CleanLayer Instance, with tracing save days
	pub fn new(day: i64, dir: String) -> Self {
		CleanLayer {
			day,
			dir,
			..Default::default()
		}
	}

	/// Set Datetime format string
	pub fn with_format(mut self, s: String) -> Self {
		self.fmt = s;
		self
	}
}

impl Default for CleanLayer {
	fn default() -> Self {
		CleanLayer {
			day: 10,
			old_expire_time: Mutex::new(Utc.datetime_from_str("2000-01-01-00-00", "%Y-%m-%d-%H-%M").unwrap()),
			dir: String::from("log"),
			fmt: String::from("%Y-%m-%d"),
		}
	}
}

fn parse_str_to_utc(s: &str, fmt: &str) -> ParseResult<DateTime<Utc>> {
	return match fmt {
		"%Y-%m-%d" => Utc.datetime_from_str(format!("{}-{}-{}", s, "00", "00").as_str(), "%Y-%m-%d-%H-%M"),
		"%Y-%m-%d-%H" => Utc.datetime_from_str(format!("{}-{}", s, "00").as_str(), "%Y-%m-%d-%H-%M"),
		_ => Utc.datetime_from_str(s, fmt)
	};
}

impl<S> Layer<S> for CleanLayer
	where
		S: Subscriber + for<'a> LookupSpan<'a>,
{
	fn on_event(&self, _event: &Event<'_>, _ctx: Context<'_, S>) {
		let current_date = Utc::today();

		let new_expire_time = (current_date - Duration::days(self.day)).and_hms(0, 0, 0);

		{
			let s = &mut *self.old_expire_time.lock();
			if new_expire_time <= *s {
				return;
			} else {
				*s = new_expire_time;
			}

		}

		let dir = Path::new(self.dir.as_str());
		if dir.is_dir() {
			if let Some(paths) = fs::read_dir(dir).ok() {
				let paths = paths
					.filter_map(|p| p.ok())
					.map(
						|p|
							(p.file_name().into_string().unwrap_or_default(),
							 p.path().into_os_string().into_string().unwrap_or_default())
					)
					.map(
						|(f, p)| (String::from(f.split(".").last().unwrap_or_default()), p)
					)
					.map(
						|(f, p)| (parse_str_to_utc(f.as_str(), self.fmt.as_str()), p))
					.filter(|(d, _)| d.is_ok() && d.unwrap() <= new_expire_time)
					.map(|(_, p)| p)
					.collect::<Vec<_>>();
				for path in paths {
					std::fs::remove_file(path).unwrap_or_default();
				}
			}
		}
	}
}


