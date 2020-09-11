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
use tracing_core::{Metadata, field::{FieldSet, Value}};

/// The Tracing Level – the user can filter by this
#[derive(Clone, Encode, Decode, Debug)]
#[cfg_attr(feature = "std", derive(PartialEq, Eq, Hash))]
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
	U64(u64),
	I64(i64),
	Bool(bool),
	Str(Vec<u8>),
	/// Debug or Display call, this is most-likely a print-able UTF8 String
	Formatted(Vec<u8>),
	/// SCALE CODEC encoded object – the name should allow the received to know
	/// how to decode this.
	Encoded(Vec<u8>),
	#[cfg(feature = "std")]
	#[codec(skip)]
	Extracted(tracing_core::field::DisplayValue<String>),
}

impl core::fmt::Debug for WasmValue {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		match self {
			WasmValue::U64(ref i) => {
				f.write_fmt(format_args!("{}_u64", i))
			}
			WasmValue::I64(ref i) => {
				f.write_fmt(format_args!("{}_i64", i))
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
			WasmValue::Extracted(ref v) => {
				f.write_fmt(format_args!("{}", v))
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

impl From<&str> for WasmValue {
	fn from(inp: &str) -> WasmValue {
		WasmValue::Str(inp.as_bytes().to_vec())
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

impl From<&FieldSet> for WasmFields {
	fn from(wm: &FieldSet) -> WasmFields {
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
	/// Whether this is a call  to `span!` or `event!`
	pub is_span: bool,
	/// The list of fields specified in the call
	pub fields: WasmFields,
}

impl From<&Metadata<'_>> for WasmMetadata {
	fn from(wm: &Metadata<'_>) -> WasmMetadata {
		WasmMetadata {
			name: wm.name().as_bytes().to_vec(),
			target: wm.target().as_bytes().to_vec(),
			level: wm.level().into(),
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

	use tracing;
	use tracing_core::{
		callsite, Level,
		field::{Value, Field, FieldSet, ValueSet, display},
		metadata::{Kind, Metadata}
	};
	use parking_lot::Mutex;
	use super::{WasmValue, WasmLevel};
	use std::collections::hash_map::HashMap;
	use lazy_static::lazy_static;

	// target, name, fieldset, level, kind
	type MetadataId = (String, String, Vec<String>, WasmLevel, bool);

	lazy_static! {
		static ref METADATA: Mutex<HashMap<MetadataId, Metadata<'static>>> = Default::default();
	}


	/// Static entry use for wasm-originated metadata.
	pub struct WasmCallsite;
	impl callsite::Callsite for WasmCallsite {
		fn set_interest(&self, _: tracing_core::Interest) { unimplemented!() }
		fn metadata(&self) -> &Metadata { unimplemented!() }
	}
	static CALLSITE: WasmCallsite =  WasmCallsite;

	/// The identifier we are using to inject the wasm events in the generic `tracing` system
	pub static WASM_TRACE_FALLBACK: &'static str = "wasm_tracing";

	fn mark_static_str<'a>(inp: &'a str) -> &'static str {
		unsafe {
			std::mem::transmute(inp)
		}
	}

	fn mark_static_slice<'a>(v : &'a[String]) -> &'static [&'static str] {
		unsafe {
			std::mem::transmute(v)
		}
	}

	fn get_metadata(
		target: String,
		name: String,
		fields: Vec<String>,
		level: WasmLevel,
		is_span: bool
	) -> &'static Metadata<'static> {

		let n = mark_static_str(name.as_str());
		let t = mark_static_str(target.as_str());
		let f = mark_static_slice(&fields[..]);
		let kind = if is_span { Kind::SPAN } else { Kind::EVENT };
		let lvl = match level {
			WasmLevel::ERROR => Level::ERROR,
			WasmLevel::WARN => Level::WARN,
			WasmLevel::INFO => Level::INFO,
			WasmLevel::DEBUG => Level::DEBUG,
			WasmLevel::TRACE => Level::TRACE,
		};

		let mut l = METADATA.lock();
		let r = l
			.entry((target, name, fields, level, is_span))
			.or_insert_with(|| {
				Metadata::new(
					n, t, lvl, None, None, None,
					FieldSet::new(f, tracing_core::identify_callsite!(&CALLSITE)),
					kind
				)
			});

		let m : &'static Metadata<'static> = unsafe {
			std::mem::transmute(r)
		};
		m
	}


	macro_rules! slice_to_values {
		($fields:expr, $slice:expr, $len:expr ) => {{
			fn this_transmute<'a>(xs: &'a [(&'a Field, Option<&'a dyn Value>)]) -> &'a [(&'a Field, Option<&'a dyn Value>); $len] {
				unsafe {
					std::mem::transmute(xs.as_ptr())
				}
			}

			$fields.value_set(this_transmute($slice))
		}}
	}

	fn run_converted<F, T>(attrs: crate::WasmEntryAttributes, f: F) -> T
	where F: Fn(&'static Metadata<'static>, &ValueSet) -> T
	{
		let metadata : &Metadata<'static> = attrs.metadata.into();
		let fields : HashMap<&str, Field> = metadata.fields()
			.iter()
			.map(|f| (f.name(), f))
			.collect();
		let mut vl = attrs.fields.0;

		let values = vl.iter_mut().filter_map(|(f, v)| {
			if let Ok(inner) = std::str::from_utf8(&f.0) {
				if let Some(field) = fields.get(inner) {
					return Some((field,
						match v {
							Some(d) => d.as_value(),
							None => None
						}
					))
				}
			}
			None
		}).collect::<Vec<_>>();

		let values = match values.len() {
			0 => metadata.fields().value_set(&[]),
			1 => slice_to_values!(metadata.fields(), values.as_slice(), 1),
			2 => slice_to_values!(metadata.fields(), values.as_slice(), 2),
			3 => slice_to_values!(metadata.fields(), values.as_slice(), 3),
			4 => slice_to_values!(metadata.fields(), values.as_slice(), 4),
			5 => slice_to_values!(metadata.fields(), values.as_slice(), 5),
			6 => slice_to_values!(metadata.fields(), values.as_slice(), 6),
			7 => slice_to_values!(metadata.fields(), values.as_slice(), 7),
			8 => slice_to_values!(metadata.fields(), values.as_slice(), 8),
			9 => slice_to_values!(metadata.fields(), values.as_slice(), 9),
			10 => slice_to_values!(metadata.fields(), values.as_slice(), 10),
			11 => slice_to_values!(metadata.fields(), values.as_slice(), 11),
			12 => slice_to_values!(metadata.fields(), values.as_slice(), 12),
			13 => slice_to_values!(metadata.fields(), values.as_slice(), 13),
			14 => slice_to_values!(metadata.fields(), values.as_slice(), 14),
			15 => slice_to_values!(metadata.fields(), values.as_slice(), 15),
			16 => slice_to_values!(metadata.fields(), values.as_slice(), 16),
			17 => slice_to_values!(metadata.fields(), values.as_slice(), 17),
			18 => slice_to_values!(metadata.fields(), values.as_slice(), 18),
			19 => slice_to_values!(metadata.fields(), values.as_slice(), 19),
			20 => slice_to_values!(metadata.fields(), values.as_slice(), 20),
			21 => slice_to_values!(metadata.fields(), values.as_slice(), 21),
			22 => slice_to_values!(metadata.fields(), values.as_slice(), 22),
			23 => slice_to_values!(metadata.fields(), values.as_slice(), 23),
			24 => slice_to_values!(metadata.fields(), values.as_slice(), 24),
			25 => slice_to_values!(metadata.fields(), values.as_slice(), 25),
			26 => slice_to_values!(metadata.fields(), values.as_slice(), 26),
			27 => slice_to_values!(metadata.fields(), values.as_slice(), 27),
			28 => slice_to_values!(metadata.fields(), values.as_slice(), 28),
			29 => slice_to_values!(metadata.fields(), values.as_slice(), 29),
			30 => slice_to_values!(metadata.fields(), values.as_slice(), 30),
			31 => slice_to_values!(metadata.fields(), values.as_slice(), 31),
			_ => slice_to_values!(metadata.fields(), &values[..32], 32),
		};

		f(metadata, &values)
	}

	fn make_hex(inp: &[u8]) -> String {
		inp.iter().map(|c| format!("{:02x}", c)).collect::<String>()
	}

	impl WasmValue {

		fn as_value<'a>(&'a mut self) -> Option<&'a dyn Value> {
			match self {
				// We convert to String
				WasmValue::Formatted(i) | WasmValue::Str(i) => {
					if let Ok(s) = String::from_utf8(i.to_vec()) {
						*self = WasmValue::Extracted(display(s))
					} else {
						*self = WasmValue::Extracted(display(make_hex(&i)))
					}
				}
				WasmValue::Encoded(i) => {
					*self = WasmValue::Extracted(display(make_hex(&i)))
				}
				_ => {}
			}

			match self {
				WasmValue::Bool(ref i) => {
					Some(i as &dyn Value)
				}
				WasmValue::U64(ref i) => {
					Some(i as &dyn Value)
				}
				WasmValue::I64(ref i) => {
					Some(i as &dyn Value)
				}
				WasmValue::Extracted(ref i) => {
					Some(i as &dyn Value)
				}
				WasmValue::Encoded(_)  | WasmValue::Formatted(_) | WasmValue::Str(_) => {
					// already dealt with above
					unreachable!()
				}
			}
		}
	}

	impl From<crate::WasmMetadata> for &'static Metadata<'static> {
		fn from(wm: crate::WasmMetadata) -> &'static Metadata<'static> {
			let name = String::from_utf8(wm.name).unwrap_or_else(|_|WASM_TRACE_FALLBACK.to_owned());
			let target = String::from_utf8(wm.target).unwrap_or_else(|_|WASM_TRACE_FALLBACK.to_owned());
			let fields = wm.fields.0.into_iter().filter_map(|s| String::from_utf8(s.0).ok()).collect();
			get_metadata(target, name, fields, wm.level, wm.is_span)
		}
	}

	impl From<crate::WasmEntryAttributes> for tracing::Span {
		fn from(a: crate::WasmEntryAttributes) -> tracing::Span {
			let parent_id = a.parent_id.map(|i|tracing_core::span::Id::from_u64(i));
			run_converted(a, move |metadata, values|
				tracing::span::Span::child_of(
					parent_id.clone(),
					metadata,
					values
				)
			)
		}
	}


	impl crate::WasmEntryAttributes {
		/// convert the given Attributes to an event and emit it using `tracing_core`.
		pub fn emit(self: crate::WasmEntryAttributes) {
			let parent_id = self.parent_id.map(|i|tracing_core::span::Id::from_u64(i));
			run_converted(self, move |metadata, values|
				tracing_core::Event::child_of(
					parent_id.clone(),
					metadata,
					values
				)
			)
		}
	}
}

#[cfg(feature = "std")]
pub use std_features::*;