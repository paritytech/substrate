// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![cfg(feature = "std")]

/// Types for working with tracing data

use std::collections::HashMap;
use std::time::Duration;

/// Represents a tracing event, complete with values
#[derive(serde::Serialize, serde::Deserialize, Clone, Debug, Default)]
pub struct TraceEvent {
	/// Event name
	pub name: String,
	/// Event target
	pub target: String,
	/// Associated `Values` of the Event
	pub values: Values,
	/// Parent id, if it exists
	pub parent_id: Option<u64>,
}

/// Represents a single instance of a tracing span
#[derive(serde::Serialize, serde::Deserialize, Clone, Debug, Default)]
pub struct SpanDatum {
	/// id for this span
	pub id: u64,
	/// id of the parent span, if any
	pub parent_id: Option<u64>,
	/// Name of this span
	pub name: String,
	/// Target, typically module
	pub target: String,
	/// Line number in source
	pub line: u32,
	/// Total duration of span while entered
	pub overall_time: Duration,
	/// Values recorded to this span
	pub values: Values,
}

/// Holds associated values for a tracing span
#[derive(serde::Serialize, serde::Deserialize, Default, Clone, Debug)]
pub struct Values {
	/// HashMap of `bool` values
	pub bool_values: HashMap<String, bool>,
	/// HashMap of `i64` values
	pub i64_values: HashMap<String, i64>,
	/// HashMap of `u64` values
	pub u64_values: HashMap<String, u64>,
	/// HashMap of `String` values
	pub string_values: HashMap<String, String>,
}

/// Container for all related spans and events
#[derive(serde::Serialize, serde::Deserialize, Clone, Debug, Default)]
pub struct Traces {
	pub spans: Vec<SpanDatum>,
	pub events: Vec<TraceEvent>,
}
