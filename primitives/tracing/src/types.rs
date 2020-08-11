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

// #![cfg_attr(not(feature = "std"), no_std)]

use sp_std::{
	vec::Vec
};
use codec::{Encode, Decode};

#[derive(Clone, Encode, Decode)]
pub enum WasmLevel {
	ERROR,
	WARN,
	INFO,
	DEBUG,
	TRACE
}

#[derive(Encode, Decode, Debug)]
pub enum WasmFieldValue {
	I64(i64),
	U64(u64),
	Bool(bool),
	Str(Vec<u8>),
	Debug(Vec<u8>),
	Encoded(Vec<u8>),
}

pub type WasmFields = Vec<Vec<u8>>;
pub type WasmValues = Vec<(Vec<u8>, WasmFieldValue)>;

#[derive(Encode, Decode)]
pub struct WasmMetadata {
	pub name: Vec<u8>,
	pub target: Vec<u8>,
	pub level: WasmLevel,
	pub file: Vec<u8>,
	pub line: u32,
	pub module_path: Vec<u8>,
	pub is_span: bool,
	pub fields: WasmFields,
}

#[derive(Encode, Decode)]
pub struct WasmAttributes {
	pub parent_id: Option<u64>,
	pub fields: WasmValues,
	pub metadata: WasmMetadata,
}

#[derive(Encode, Decode)]
pub struct WasmEvent {
	pub parent_id: Option<u64>,
	pub metadata: WasmMetadata,
	pub fields: WasmValues,
}

// TODO - Do we need this when we have WasmValues ?
// #[derive(Encode, Decode)]
// pub struct WasmRecord;

#[cfg(feature = "std")]
impl From<WasmLevel> for tracing::Level {
	fn from(w: WasmLevel) -> Self {
		match w {
			WasmLevel::ERROR => tracing::Level::ERROR,
			WasmLevel::WARN => tracing::Level::WARN,
			WasmLevel::INFO => tracing::Level::INFO,
			WasmLevel::DEBUG => tracing::Level::DEBUG,
			WasmLevel::TRACE => tracing::Level::TRACE,
		}
	}
}

#[cfg(feature = "std")]
impl WasmMetadata {
	pub fn target(&self) -> &str {
		std::str::from_utf8(&self.target).unwrap()
	}

	pub fn name(&self) -> &str {
		std::str::from_utf8(&self.name).unwrap()
	}

	pub fn level(&self) -> tracing::Level {
		self.level.clone().into()
	}
}
