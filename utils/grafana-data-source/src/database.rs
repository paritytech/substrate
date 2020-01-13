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

use std::collections::HashMap;
use std::convert::TryFrom;
use crate::Error;

pub struct Database {
	base_timestamp: i64,
	storage: HashMap<String, Vec<Datapoint>>
}

impl Database {
	/// Create a new Database.
	pub fn new() -> Self {
		Self {
			base_timestamp: now_millis(),
			storage: HashMap::new()
		}
	}

	/// Produce an iterator for keys starting with a base string.
	pub fn keys_starting_with<'a>(&'a self, base: &'a str) -> impl Iterator<Item = String> + 'a {
		self.storage.keys()
			.filter(move |key| key.starts_with(base))
			.cloned()
	}

	/// Select `max_datapoints` datapoints that have been added between `from` and `to`.
	pub fn datapoints_between(&self, key: &str, from: i64, to: i64, max_datapoints: usize) -> Option<Vec<(f32, i64)>> {
		self.storage.get(key)
			.map(|vec| {
				let from = find_index(vec, self.base_timestamp, from);
				let to = find_index(vec, self.base_timestamp, to);
				let slice = &vec[from .. to];

				if max_datapoints == 0 {
					Vec::new()
				} else if max_datapoints >= slice.len() {
					// Just convert the slice as-is
					slice.iter()
						.map(|dp| dp.make_absolute(self.base_timestamp))
						.collect()
				} else {
					// We have more datapoints than we need, so we need to skip some
					(0 .. max_datapoints - 1)
						.map(|i| &slice[i * slice.len() / (max_datapoints - 1)])
						.chain(slice.last())
						.map(|dp| dp.make_absolute(self.base_timestamp))
						.collect()
				}
			})
	}

	/// Push a new datapoint. Will error if the base timestamp hasn't been updated in `2^32`
	/// milliseconds (49 days).
	pub fn push(&mut self, key: &str, value: f32) -> Result<(), Error> {
		self.storage.entry(key.into())
			.or_insert_with(Vec::new)
			.push(Datapoint::new(self.base_timestamp, value)?);

		Ok(())
	}

	/// Set a new base timestamp, and remove metrics older than this new timestamp. Errors if the
	/// difference between timestamps is greater than `2^32` milliseconds (49 days).
	pub fn truncate(&mut self, new_base_timestamp: i64) -> Result<(), Error> {
		// Ensure that the new base is older.
		if self.base_timestamp >= new_base_timestamp {
			return Ok(());
		}

		// If the old base timestamp was too long ago, the
		let delta = u32::try_from(new_base_timestamp - self.base_timestamp)
			.map_err(Error::Timestamp)?;

		for metric in self.storage.values_mut() {
			// Find the index of the oldest allowed timestamp and cut out all those before it.
			let index = find_index(&metric, self.base_timestamp, new_base_timestamp);

			*metric = metric.iter_mut()
				.skip(index)
				.map(|dp| {
					dp.delta_timestamp -= delta;
					*dp
				})
				.collect();
		}

		self.base_timestamp = new_base_timestamp;

		Ok(())
	}
}

#[derive(Clone, Copy)]
struct Datapoint {
	delta_timestamp: u32,
	value: f32
}

impl Datapoint {
	fn new(base_timestamp: i64, value: f32) -> Result<Self, Error> {
		Ok(Self {
			delta_timestamp: u32::try_from(now_millis() - base_timestamp)
				.map_err(Error::Timestamp)?,
			value
		})
	}

	fn make_absolute(self, base_timestamp: i64) -> (f32, i64) {
		(self.value, base_timestamp + self.delta_timestamp as i64)
	}
}

fn find_index(slice: &[Datapoint], base_timestamp: i64, timestamp: i64) -> usize {
	slice.binary_search_by_key(&timestamp, |datapoint| {
		base_timestamp + datapoint.delta_timestamp as i64
	}).unwrap_or_else(|index| index)
}

/// Get the current unix timestamp in milliseconds.
fn now_millis() -> i64 {
	chrono::Utc::now().timestamp_millis()
}

#[test]
fn test() {
	let mut database = Database::new();

	database.push("test", 1.0).unwrap();
	database.push("test", 2.5).unwrap();
	database.push("test", 2.0).unwrap();
	database.push("test 2", 1.0).unwrap();

	let mut keys: Vec<_> = database.keys_starting_with("test").collect();
	keys.sort();

	assert_eq!(keys, ["test", "test 2"]);
	assert_eq!(database.keys_starting_with("test ").collect::<Vec<_>>(), ["test 2"]);
}
