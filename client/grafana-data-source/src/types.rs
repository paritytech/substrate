// Copyright 2019 Parity Technologies (UK) Ltd.
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

use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
pub struct Target {
	pub target: String,
}

#[derive(Serialize, Deserialize)]
pub struct Query {
	#[serde(rename = "maxDataPoints")]
	pub max_datapoints: usize,
	pub targets: Vec<Target>,
	pub range: Range,
}

#[derive(Serialize, Deserialize)]
pub struct Range {
	#[serde(deserialize_with = "date_to_timestamp_ms")]
	pub from: i64,
	#[serde(deserialize_with = "date_to_timestamp_ms")]
	pub to: i64,
}

// Deserialize a timestamp via a `DateTime<Utc>`
fn date_to_timestamp_ms<'de, D: serde::Deserializer<'de>>(timestamp: D) -> Result<i64, D::Error> {
	Deserialize::deserialize(timestamp)
		.map(|date: chrono::DateTime<chrono::Utc>| date.timestamp_millis())
}

#[derive(Serialize, Deserialize)]
pub struct TimeseriesData {
	pub target: String,
	pub datapoints: Vec<(f32, i64)>
}
