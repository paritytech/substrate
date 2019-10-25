use serde::{Serialize, Deserialize};
use chrono::{DateTime, Utc};

#[derive(Serialize, Deserialize, Debug)]
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

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct QueryRequest {
	interval_ms: u64,
	max_data_points: u64,
	pub targets: Vec<Target>,
	pub range: Range,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Target {
	pub target: String,
	#[serde(rename = "type")]
	target_type: TargetType,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Range {
	pub from: DateTime<Utc>,
	pub to: DateTime<Utc>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct TimeseriesData {
	pub target: String,
	pub datapoints: Vec<(f32, u64)>
}
