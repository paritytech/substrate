// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Types for working with tracing data

use serde::{Deserialize, Serialize};

use rustc_hash::FxHashMap;

/// Container for all related spans and events for the block being traced.
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
pub struct BlockTrace {
	/// Hash of the block being traced
	pub block_hash: String,
	/// Parent hash
	pub parent_hash: String,
	/// Module targets that were recorded by the tracing subscriber.
	/// Empty string means record all targets.
	pub tracing_targets: String,
	/// Storage key targets used to filter out events that do not have one of the storage keys.
	/// Empty string means do not filter out any events.
	pub storage_keys: String,
	/// Method targets used to filter out events that do not have one of the event method.
	/// Empty string means do not filter out any events.
	pub methods: String,
	/// Vec of tracing spans
	pub spans: Vec<Span>,
	/// Vec of tracing events
	pub events: Vec<Event>,
}

/// Represents a tracing event, complete with recorded data.
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Event {
	/// Event target
	pub target: String,
	/// Associated data
	pub data: Data,
	/// Parent id, if it exists
	pub parent_id: Option<u64>,
}

/// Represents a single instance of a tracing span.
///
/// Exiting a span does not imply that the span will not be re-entered.
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Span {
	/// id for this span
	pub id: u64,
	/// id of the parent span, if any
	pub parent_id: Option<u64>,
	/// Name of this span
	pub name: String,
	/// Target, typically module
	pub target: String,
	/// Indicates if the span is from wasm
	pub wasm: bool,
}

/// Holds associated values for a tracing span.
#[derive(Serialize, Deserialize, Default, Clone, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Data {
	/// HashMap of `String` values recorded while tracing
	pub string_values: FxHashMap<String, String>,
}

/// Error response for the `state_traceBlock` RPC.
#[derive(Serialize, Deserialize, Default, Clone, Debug)]
#[serde(rename_all = "camelCase")]
pub struct TraceError {
	/// Error message
	pub error: String,
}

/// Response for the `state_traceBlock` RPC.
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
pub enum TraceBlockResponse {
	/// Error block tracing response
	TraceError(TraceError),
	/// Successful block tracing response
	BlockTrace(BlockTrace),
}
