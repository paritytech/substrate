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

/// Types for wasm based tracing. Loosly inspired by `tracing-core` but
/// optimised for the specific use case.

use core::{format_args, fmt::Debug};
use sp_std::{
	vec, vec::Vec,
};
use sp_std::Writer;
use codec::{Encode, Decode};

/// The Tracing Level – the user can filter by this
#[derive(Clone, Encode, Decode, Debug)]
pub enum WasmLevel {
	/// This is a fatal errors
	ERROR,
	/// This is a warning you should be aware of
	WARN,
	/// Nice to now info
	INFO,
	/// Further information for debugging purposes
	DEBUG,
	/// The lowest level, keeping track of minute detail
	TRACE
}


impl From<&tracing_core::Level> for WasmLevel {
	fn from(l: &tracing_core::Level) -> WasmLevel {
		match l {
			&tracing_core::Level::ERROR => WasmLevel::ERROR,
			&tracing_core::Level::WARN => WasmLevel::WARN,
			&tracing_core::Level::INFO => WasmLevel::INFO,
			&tracing_core::Level::DEBUG => WasmLevel::DEBUG,
			&tracing_core::Level::TRACE => WasmLevel::TRACE,
		}
	}
}



impl core::default::Default for WasmLevel {
	fn default() -> Self {
		WasmLevel::TRACE
	}
}

/// A paramter value provided to the span/event
#[derive(Encode, Decode, Clone)]
pub enum WasmValue {
	U8(u8),
	I8(i8),
	U32(u32),
	I32(i32),
	I64(i64),
	U64(u64),
	Bool(bool),
	Str(Vec<u8>),
	/// Debug or Display call, this is most-likely a print-able UTF8 String
	Formatted(Vec<u8>),
	/// SCALE CODEC encoded object – the name should allow the received to know
	/// how to decode this.
	Encoded(Vec<u8>),
}

impl core::fmt::Debug for WasmValue {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		match self {
			WasmValue::U8(ref i) => {
				f.write_fmt(format_args!("{}_u8", i))
			}
			WasmValue::I8(ref i) => {
				f.write_fmt(format_args!("{}_i8", i))
			}
			WasmValue::U32(ref i) => {
				f.write_fmt(format_args!("{}_u32", i))
			}
			WasmValue::I32(ref i) => {
				f.write_fmt(format_args!("{}_i32", i))
			}
			WasmValue::I64(ref i) => {
				f.write_fmt(format_args!("{}_i64", i))
			}
			WasmValue::U64(ref i) => {
				f.write_fmt(format_args!("{}_u64", i))
			}
			WasmValue::Bool(ref i) => {
				f.write_fmt(format_args!("{}_bool", i))
			}
			WasmValue::Formatted(ref i) | WasmValue::Str(ref i) => {
				if let Ok(v) = core::str::from_utf8(i) {
					f.write_fmt(format_args!("{}", v))
				} else {
					f.write_fmt(format_args!("{:?}", i))
				}
			}
			WasmValue::Encoded(ref v) => {
				f.write_str("Scale(")?;
					for byte in v {
						f.write_fmt(format_args!("{:02x}", byte))?;
					}
				f.write_str(")")
			}
		}
	}
}

impl From<u8> for WasmValue {
	fn from(u: u8) -> WasmValue {
		WasmValue::U8(u)
	}
}

impl From<&i8> for WasmValue {
	fn from(inp: &i8) -> WasmValue {
		WasmValue::I8(inp.clone())
	}
}

impl From<&str> for WasmValue {
	fn from(inp: &str) -> WasmValue {
		WasmValue::Str(inp.as_bytes().to_vec())
	}
}

impl From<&&str> for WasmValue {
	fn from(inp: &&str) -> WasmValue {
		WasmValue::Str((*inp).as_bytes().to_vec())
	}
}

impl From<bool> for WasmValue {
	fn from(inp: bool) -> WasmValue {
		WasmValue::Bool(inp)
	}
}

impl From<core::fmt::Arguments<'_>> for WasmValue {
	fn from(inp: core::fmt::Arguments<'_>) -> WasmValue {
		let mut buf = Writer::default();
		core::fmt::write(&mut buf, inp).expect("Writing of arguments doesn't fail");
		WasmValue::Formatted(buf.into_inner())
	}
}

impl From<i8> for WasmValue {
	fn from(u: i8) -> WasmValue {
		WasmValue::I8(u)
	}
}

impl From<i32> for WasmValue {
	fn from(u: i32) -> WasmValue {
		WasmValue::I32(u)
	}
}

impl From<&i32> for WasmValue {
	fn from(u: &i32) -> WasmValue {
		WasmValue::I32(*u)
	}
}

impl From<u32> for WasmValue {
	fn from(u: u32) -> WasmValue {
		WasmValue::U32(u)
	}
}

impl From<&u32> for WasmValue {
	fn from(u: &u32) -> WasmValue {
		WasmValue::U32(*u)
	}
}

impl From<u64> for WasmValue {
	fn from(u: u64) -> WasmValue {
		WasmValue::U64(u)
	}
}

impl From<i64> for WasmValue {
	fn from(u: i64) -> WasmValue {
		WasmValue::I64(u)
	}
}

/// The name of a field provided as the argument name when contstructing an
/// `event!` or `span!`.
/// Generally generated automaticaly via `stringify` from an `'static &str`.
/// Likely print-able.
#[derive(Encode, Decode, Clone)]
pub struct WasmFieldName(Vec<u8>);

impl core::fmt::Debug for WasmFieldName {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		if let Ok(v) = core::str::from_utf8(&self.0) {
			f.write_fmt(format_args!("{}", v))
		} else {
			for byte in self.0.iter() {
				f.write_fmt(format_args!("{:02x}", byte))?;
			}
			Ok(())
		}
	}
}

impl From<Vec<u8>> for WasmFieldName {
	fn from(v: Vec<u8>) -> Self {
		WasmFieldName(v)
	}
}

impl From<&str> for WasmFieldName {
	fn from(v: &str) -> Self {
		WasmFieldName(v.as_bytes().to_vec())
	}
}

/// A list of `WasmFieldName`s in the order provided
#[derive(Encode, Decode, Clone, Debug)]
pub struct WasmFields(Vec<WasmFieldName>);

impl WasmFields {
	/// Iterate over the fields
	pub fn iter(&self) -> core::slice::Iter<'_, WasmFieldName> {
		self.0.iter()
	}
}

impl From<Vec<WasmFieldName>> for WasmFields {
	fn from(v: Vec<WasmFieldName>) -> WasmFields {
		WasmFields(v.into())
	}
}

impl From<Vec<&str>> for WasmFields {
	fn from(v: Vec<&str>) -> WasmFields {
		WasmFields(v.into_iter().map(|v| v.into()).collect())
	}
}

impl WasmFields {
	/// Create an empty entry
	pub fn empty() -> Self {
		WasmFields(Vec::with_capacity(0))
	}
}

impl From<&tracing_core::field::FieldSet> for WasmFields {
	fn from(wm: &tracing_core::field::FieldSet) -> WasmFields {
		WasmFields(wm.iter().map(|s| s.name().into()).collect())
	}
}

/// A list of `WasmFieldName`s with the given `WasmValue` (if provided)
/// in the order specified.
#[derive(Encode, Decode, Clone)]
pub struct WasmValuesSet(Vec<(WasmFieldName, Option<WasmValue>)>);

impl core::fmt::Debug for WasmValuesSet {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		let mut wrt = f.debug_struct("");
		let mut non_str = false;
		for (f, v) in self.0.iter() {
			if let Ok(s) = core::str::from_utf8(&f.0) {
				match v {
					Some(ref i) => wrt.field(s, i),
					None => wrt.field(s, &(None as Option<WasmValue>)),
				};
			} else {
				non_str = true;
			}
		}

		// FIXME: replace with using `finish_non_exhaustive()` once stable
		//        https://github.com/rust-lang/rust/issues/67364
		if non_str {
			wrt.field("..", &"..");
		}

		wrt.finish()
	}
}


impl From<Vec<(WasmFieldName, Option<WasmValue>)>> for WasmValuesSet {
	fn from(v: Vec<(WasmFieldName, Option<WasmValue>)>) -> Self {
		WasmValuesSet(v)
	}
}
impl From<Vec<(&&WasmFieldName, Option<WasmValue>)>> for WasmValuesSet {
	fn from(v: Vec<(&&WasmFieldName, Option<WasmValue>)>) -> Self {
		WasmValuesSet(v.into_iter().map(|(k, v)| ((**k).clone(), v)).collect())
	}
}

impl From<Vec<(&&str, Option<WasmValue>)>> for WasmValuesSet {
	fn from(v: Vec<(&&str, Option<WasmValue>)>) -> Self {
		WasmValuesSet(v.into_iter().map(|(k, v)| ((*k).into(), v)).collect())
	}
}

impl WasmValuesSet {
	/// Create an empty entry
	pub fn empty() -> Self {
		WasmValuesSet(Vec::with_capacity(0))
	}
}

impl tracing_core::field::Visit for WasmValuesSet {
	fn record_debug(&mut self, field: &tracing_core::field::Field, value: &dyn Debug) {
		self.0.push( (
			field.name().into(),
			Some(WasmValue::from(format_args!("{:?}", value)))
		))
	}
	fn record_i64(&mut self, field: &tracing_core::field::Field, value: i64) {
		self.0.push( (
			field.name().into(),
			Some(WasmValue::from(value))
		))
	}
	fn record_u64(&mut self, field: &tracing_core::field::Field, value: u64) {
		self.0.push( (
			field.name().into(),
			Some(WasmValue::from(value))
		))
	}
	fn record_bool(&mut self, field: &tracing_core::field::Field, value: bool) {
		self.0.push( (
			field.name().into(),
			Some(WasmValue::from(value))
		))
	}
	fn record_str(&mut self, field: &tracing_core::field::Field, value: &str) {
		self.0.push( (
			field.name().into(),
			Some(WasmValue::from(value))
		))
	}
}
/// Metadata provides generic information about the specifc location of the
/// `span!` or `event!` call on the wasm-side.
#[derive(Encode, Decode, Clone)]
pub struct WasmMetadata {
	/// The name given to `event!`/`span!`, `&'static str` converted to bytes
	pub name: Vec<u8>,
	/// The given target to `event!`/`span!` – or module-name, `&'static str` converted to bytes
	pub target: Vec<u8>,
	/// The level of this entry
	pub level: WasmLevel,
	/// The file this was emitted from – useful for debugging;  `&'static str` converted to bytes
	pub file: Vec<u8>,
	/// The specific line number in the file – useful for debugging
	pub line: u32,
	/// The module path;  `&'static str` converted to bytes
	pub module_path: Vec<u8>,
	/// Whether this is a call  to `span!` or `event!`
	pub is_span: bool,
	/// The list of fields specified in the call
	pub fields: WasmFields,
}

impl From<&tracing_core::Metadata<'_>> for WasmMetadata {
	fn from(wm: &tracing_core::Metadata<'_>) -> WasmMetadata {
		WasmMetadata {
			name: wm.name().as_bytes().to_vec(),
			target: wm.target().as_bytes().to_vec(),
			level: wm.level().into(),
			file: wm.file().map(|f| f.as_bytes().to_vec()).unwrap_or_default(),
			line: wm.line().unwrap_or_default(),
			module_path: wm.module_path().map(|m| m.as_bytes().to_vec()).unwrap_or_default(),
			is_span: wm.is_span(),
			fields: wm.fields().into()
		}
	}
}

impl core::fmt::Debug for WasmMetadata {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.debug_struct("WasmMetadata")
			.field("name", &decode_field(&self.name))
			.field("target", &decode_field(&self.target))
			.field("level", &self.level)
			.field("file", &decode_field(&self.file))
			.field("line", &self.line)
			.field("module_path", &decode_field(&self.module_path))
			.field("is_span", &self.is_span)
			.field("fields", &self.fields)
			.finish()
	}
}

impl core::default::Default for WasmMetadata {
	fn default() -> Self {
		let target = "default".as_bytes().to_vec();
		WasmMetadata {
			target,
			name: Default::default(),
			level: Default::default(),
			file: Default::default(),
			line: Default::default(),
			module_path: Default::default(),
			is_span: true,
			fields: WasmFields::empty()
		}
	}
}


fn decode_field(field: &[u8]) -> &str {
	core::str::from_utf8(field).unwrap_or_default()
}

/// Span or Event Attributes
#[derive(Encode, Decode, Clone, Debug)]
pub struct WasmEntryAttributes {
	/// the parent, if directly specified – otherwise assume most inner span
	pub parent_id: Option<u64>,
	/// the metadata of the location
	pub metadata: WasmMetadata,
	/// the Values provided
	pub fields: WasmValuesSet,
}

impl From<&tracing_core::Event<'_>> for WasmEntryAttributes {
	fn from(evt: &tracing_core::Event<'_>) -> WasmEntryAttributes {
		let mut fields = WasmValuesSet(Vec::new());
		evt.record(&mut fields);
		WasmEntryAttributes {
			parent_id: evt.parent().map(|id| id.into_u64()),
			metadata: evt.metadata().into(),
			fields: fields
		}
	}
}

impl From<&tracing_core::span::Attributes<'_>> for WasmEntryAttributes {
	fn from(attrs: &tracing_core::span::Attributes<'_>) -> WasmEntryAttributes {
		let mut fields = WasmValuesSet(Vec::new());
		attrs.record(&mut fields);
		WasmEntryAttributes {
			parent_id: attrs.parent().map(|id| id.into_u64()),
			metadata: attrs.metadata().into(),
			fields: fields
		}
	}
}

impl core::default::Default for WasmEntryAttributes {
	fn default() -> Self {
		WasmEntryAttributes {
			parent_id: None,
			metadata: Default::default(),
			fields: WasmValuesSet(vec![]),
		}
	}
}

#[cfg(feature = "std")]
mod std_features {

	use tracing_core::callsite;
	use tracing;

	/// Static entry use for wasm-originated metadata.
	pub struct WasmCallsite;
	impl callsite::Callsite for WasmCallsite {
		fn set_interest(&self, _: tracing_core::Interest) { unimplemented!() }
		fn metadata(&self) -> &tracing_core::Metadata { unimplemented!() }
	}
	static CALLSITE: WasmCallsite =  WasmCallsite;
	/// The identifier we are using to inject the wasm events in the generic `tracing` system
	pub static WASM_TRACE_IDENTIFIER: &'static str = "wasm_tracing";
	/// The fieldname for the wasm-originated name
	pub static WASM_NAME_KEY: &'static str = "name";
	/// The fieldname for the wasm-originated target
	pub static WASM_TARGET_KEY: &'static str = "target";
	/// The the list of all static field names we construct from the given metadata
	pub static GENERIC_FIELDS: &'static [&'static str] = &[WASM_TARGET_KEY, WASM_NAME_KEY,
		"file", "line", "module_path", "params"];

	// Implementation Note:
	// the original `tracing` crate generates these static metadata entries at every `span!` and
	// `event!` location to allow for highly optimised filtering. For us to allow level-based emitting
	// of wasm events we need these static metadata entries to inject into that system. We then provide
	// generic `From`-implementations picking the right metadata to refer to.

	static SPAN_ERROR_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACE_IDENTIFIER, WASM_TRACE_IDENTIFIER, tracing::Level::ERROR, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::SPAN
	);

	static SPAN_WARN_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACE_IDENTIFIER, WASM_TRACE_IDENTIFIER, tracing::Level::WARN, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::SPAN
	);
	static SPAN_INFO_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACE_IDENTIFIER, WASM_TRACE_IDENTIFIER, tracing::Level::INFO, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::SPAN
	);

	static SPAN_DEBUG_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACE_IDENTIFIER, WASM_TRACE_IDENTIFIER, tracing::Level::DEBUG, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::SPAN
	);

	static SPAN_TRACE_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACE_IDENTIFIER, WASM_TRACE_IDENTIFIER, tracing::Level::TRACE, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::SPAN
	);

	static EVENT_ERROR_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACE_IDENTIFIER, WASM_TRACE_IDENTIFIER, tracing::Level::ERROR, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::EVENT
	);

	static EVENT_WARN_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACE_IDENTIFIER, WASM_TRACE_IDENTIFIER, tracing::Level::WARN, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::EVENT
	);

	static EVENT_INFO_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACE_IDENTIFIER, WASM_TRACE_IDENTIFIER, tracing::Level::INFO, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::EVENT
	);

	static EVENT_DEBUG_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACE_IDENTIFIER, WASM_TRACE_IDENTIFIER, tracing::Level::DEBUG, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::EVENT
	);

	static EVENT_TRACE_METADATA : tracing_core::Metadata<'static> = tracing::Metadata::new(
		WASM_TRACE_IDENTIFIER, WASM_TRACE_IDENTIFIER, tracing::Level::TRACE, None, None, None,
		tracing_core::field::FieldSet::new(GENERIC_FIELDS, tracing_core::identify_callsite!(&CALLSITE)),
		tracing_core::metadata::Kind::EVENT
	);

	// FIXME: this could be done a lot in 0.2 if they opt for using `Cow<str,'static>` instead
	//			https://github.com/paritytech/substrate/issues/7134
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

	impl From<crate::WasmEntryAttributes> for tracing::Span {
		fn from(a: crate::WasmEntryAttributes) -> tracing::Span {
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

	impl crate::WasmEntryAttributes {
		/// convert the given Attributes to an event and emit it using `tracing_core`.
		pub fn emit(self: crate::WasmEntryAttributes) {
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
