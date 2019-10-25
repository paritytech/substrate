// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use chrono::{DateTime, Utc};

#[derive(Serialize, Deserialize)]
pub enum TargetType {
	#[serde(rename = "timeseries")]
	Timeseries,
	#[serde(rename = "table")]
	Table
}

#[derive(Serialize, Deserialize)]
pub struct SearchRequest {
	pub target: String
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct QueryRequest {
	interval_ms: u64,
	max_data_points: u64,
	pub targets: Vec<Target>,
	pub range: Range,
}

#[derive(Serialize, Deserialize)]
pub struct Target {
	pub target: String,
	#[serde(rename = "type")]
	target_type: TargetType,
}

#[derive(Serialize, Deserialize)]
pub struct Range {
	pub from: DateTime<Utc>,
	pub to: DateTime<Utc>,
}

#[derive(Serialize, Deserialize)]
pub struct TimeseriesData {
	pub target: String,
	pub datapoints: Vec<(f32, i64)>
}
