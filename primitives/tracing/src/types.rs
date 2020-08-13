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

use core::fmt::Debug;
use sp_std::{
	vec::Vec
};
use codec::{Encode, Decode};

#[derive(Clone, Encode, Decode, Debug)]
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

#[derive(Encode, Decode, Debug)]
pub struct WasmValues(Vec<(Vec<u8>, WasmFieldValue)>);

impl From<Vec<(Vec<u8>, WasmFieldValue)>> for WasmValues {
	fn from(v: Vec<(Vec<u8>, WasmFieldValue)>) -> Self {
		WasmValues(v)
	}
}

#[derive(Encode, Decode, Debug)]
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

#[derive(Encode, Decode, Debug)]
pub struct WasmAttributes {
	pub parent_id: Option<u64>,
	pub metadata: WasmMetadata,
	pub fields: WasmValues,
}

#[derive(Encode, Decode, Debug)]
pub struct WasmEvent {
	pub parent_id: Option<u64>,
	pub metadata: WasmMetadata,
	pub fields: WasmValues,
}

// TODO - Do we need this when we have WasmValues ?
// #[derive(Encode, Decode)]
// pub struct WasmRecord;


#[cfg(feature = "std")]
mod std_features {

	use tracing_core::callsite;
	use tracing;

	pub struct WasmCallsite;
	impl callsite::Callsite for WasmCallsite {
		fn set_interest(&self, _: tracing_core::Interest) { unimplemented!() }
		fn metadata(&self) -> &tracing_core::Metadata { unimplemented!() }
	}
	static CALLSITE: WasmCallsite =  WasmCallsite;
	static WASM_TRACING_NAME: &'static str = "wasm_tracing";
	static GENERIC_FIELDS: &'static [&'static str] = &["target", "name", "file", "line", "module_path", "params"];

	static SPAN_ERROR_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACING_NAME, WASM_TRACING_NAME, tracing::Level::ERROR, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::SPAN
	);

	static SPAN_WARN_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACING_NAME, WASM_TRACING_NAME, tracing::Level::WARN, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::SPAN
	);
	static SPAN_INFO_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACING_NAME, WASM_TRACING_NAME, tracing::Level::INFO, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::SPAN
	);

	static SPAN_DEBUG_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACING_NAME, WASM_TRACING_NAME, tracing::Level::DEBUG, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::SPAN
	);

	static SPAN_TRACE_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACING_NAME, WASM_TRACING_NAME, tracing::Level::TRACE, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::SPAN
	);

	static EVENT_ERROR_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACING_NAME, WASM_TRACING_NAME, tracing::Level::ERROR, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::EVENT
	);

	static EVENT_WARN_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACING_NAME, WASM_TRACING_NAME, tracing::Level::WARN, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::EVENT
	);

	static EVENT_INFO_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACING_NAME, WASM_TRACING_NAME, tracing::Level::INFO, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::EVENT
	);

	static EVENT_DEBUG_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACING_NAME, WASM_TRACING_NAME, tracing::Level::DEBUG, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::EVENT
	);

	static EVENT_TRACE_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACING_NAME, WASM_TRACING_NAME, tracing::Level::TRACE, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::EVENT
	);

	impl From<&crate::WasmMetadata> for &'static tracing_core::Metadata<'static> {
		fn from(wm: &crate::WasmMetadata) -> &'static tracing_core::Metadata<'static> {
			match (&wm.level, wm.is_span) {
				(&crate::WasmLevel::ERROR, true) => &SPAN_ERROR_METADATA,
				(&crate::WasmLevel::WARN, true) => &SPAN_WARN_METADATA,
				(&crate::WasmLevel::INFO, true) => &SPAN_INFO_METADATA,
				(&crate::WasmLevel::DEBUG, true) => &SPAN_DEBUG_METADATA,
				(&crate::WasmLevel::TRACE, true) => &SPAN_TRACE_METADATA,
				(&crate::WasmLevel::ERROR, false) => &EVENT_ERROR_METADATA,
				(&crate::WasmLevel::WARN, false) => &EVENT_WARN_METADATA,
				(&crate::WasmLevel::INFO, false) => &EVENT_INFO_METADATA,
				(&crate::WasmLevel::DEBUG, false) => &EVENT_DEBUG_METADATA,
				(&crate::WasmLevel::TRACE, false) => &EVENT_TRACE_METADATA,
			}
		}
	}

	impl From<crate::WasmAttributes> for tracing::Span {
		fn from(a: crate::WasmAttributes) -> tracing::Span {
			let name = std::str::from_utf8(&a.metadata.name).unwrap_or_default();
			let target = std::str::from_utf8(&a.metadata.target).unwrap_or_default();
			let file = std::str::from_utf8(&a.metadata.file).unwrap_or_default();
			let line = a.metadata.line;
			let module_path = std::str::from_utf8(&a.metadata.module_path).unwrap_or_default();
			let params = a.fields;
			let metadata : &tracing_core::metadata::Metadata<'static> = (&a.metadata).into();

			tracing::span::Span::child_of(
				a.parent_id.map(|i|tracing_core::span::Id::from_u64(i)), 
				&metadata,
				&tracing::valueset!{ metadata.fields(), target, name, file, line, module_path, ?params }
			)
		}
	}

	impl crate::WasmEvent {
		pub fn emit(self: crate::WasmEvent) {
			let name = std::str::from_utf8(&self.metadata.name).unwrap_or_default();
			let target = std::str::from_utf8(&self.metadata.target).unwrap_or_default();
			let file = std::str::from_utf8(&self.metadata.file).unwrap_or_default();
			let line = self.metadata.line;
			let module_path = std::str::from_utf8(&self.metadata.module_path).unwrap_or_default();
			let params = self.fields;
			let metadata : &tracing_core::metadata::Metadata<'static> = (&self.metadata).into();

			tracing_core::Event::child_of(
				self.parent_id.map(|i|tracing_core::span::Id::from_u64(i)), 
				&metadata,
				&tracing::valueset!{ metadata.fields(), target, name, file, line, module_path, ?params }
			)
		}
	}
}

#[cfg(feature = "std")]
pub use std_features::*;