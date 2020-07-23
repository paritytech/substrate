// Copyright 2020 Parity Technologies (UK) Ltd.
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

#![cfg_attr(not(feature = "std"), no_std)]
//! Proxy to allow entering tracing spans from wasm.
use core::{
	default::Default,
	fmt::Debug,
};
use codec::{Encode, Decode};
use tracing_core::{
	subscriber::Subscriber,
	metadata::Metadata,
	field::{Field, Visit},
	event::{Event},
	span::{
		Attributes,
		Id,
		Record,
	},
	Level,
};

struct WasmProxySubscriber;
impl Subscriber for WasmProxySubscriber {
	fn enabled(&self, metadata: &Metadata) -> bool {
		todo!{}
		// host_functions::tracing_enabled(metadata.into())
	}
	fn record_follows_from(&self, span: &Id, follows: &Id) {
		todo!{}
		// host_functions::tracing_record_follows_from(span.into_u64(), follows.into_u64())
	}
	fn new_span(&self, span: &Attributes) -> Id {
		todo!{}
		// Id::from_u64(host_functions::tracing_new_span(span.into())
	}
	fn record(&self, span: &Id, values: &Record) {
		todo!{}
		// host_functions::tracing_record(span.into_u64(), value.into())
	}
	fn event(&self, event: &Event) {
		todo!{}
		// host_functions::tracing_enter(event.into())
	}
	fn enter(&self, span: &Id) {
		todo!{}
		// host_functions::tracing_enter(span.into_u64())
	}
	fn exit(&self, span: &Id) {
		todo!{}
		// host_functions::tracing_exit(span.into_u64())
	}
}

#[derive(Encode, Decode)]
pub enum FieldValue {
	I64(i64),
	U64(u64),
	Bool(bool),
	Str(Vec<u8>),
	Debug(Vec<u8>),
}


#[derive(Encode, Decode)]
pub struct Fields (pub Vec<(Vec<u8>, FieldValue)>);

impl Visit for Fields {
	fn record_debug(&mut self, field: &Field, value: &dyn Debug) {
		todo!{}
		// self.0.push((field.name().as_bytes().into(), FieldValue::Debug(format!("{:?}", value).into())));
	}
	fn record_i64(&mut self, field: &Field, value: i64) {
		self.0.push((field.name().as_bytes().into(), FieldValue::I64(value)));
	}
	fn record_u64(&mut self, field: &Field, value: u64) {
		self.0.push((field.name().as_bytes().into(), FieldValue::U64(value)));
	}
	fn record_bool(&mut self, field: &Field, value: bool) {
		self.0.push((field.name().as_bytes().into(), FieldValue::Bool(value)));
	}
	fn record_str(&mut self, field: &Field, value: &str) {
		self.0.push((field.name().as_bytes().into(), FieldValue::Str(value.as_bytes().into())));
	}
}

#[derive(Encode, Decode)]
pub struct TracingAttributes {
	pub parent_id: Option<u64>,
	pub fields: Fields
}

impl From<&Attributes<'_>> for TracingAttributes {
	fn from(a: &Attributes) -> TracingAttributes {
		let mut fields = Fields(Vec::new());
		a.record(&mut fields);
		TracingAttributes {
			parent_id: a.parent().map(|a| a.into_u64()),
			fields
		}
	}
}


#[derive(Encode, Decode)]
pub enum TracingLevel {
	ERROR,
	WARN,
	INFO,
	DEBUG,
	TRACE
}

impl From<&Level> for TracingLevel {
	fn from(lvl: &Level) -> TracingLevel {
		match *lvl {
			Level::ERROR => TracingLevel::ERROR,
			Level::WARN => TracingLevel::WARN,
			Level::INFO => TracingLevel::INFO,
			Level::DEBUG => TracingLevel::DEBUG,
			Level::TRACE => TracingLevel::TRACE,
		}
	}
}

impl Into<Level> for TracingLevel {
	fn into(self) -> Level {
		match self {
			TracingLevel::ERROR => Level::ERROR,
			TracingLevel::WARN => Level::WARN,
			TracingLevel::INFO => Level::INFO,
			TracingLevel::DEBUG => Level::DEBUG,
			TracingLevel::TRACE => Level::TRACE,
		}
	}
}

#[derive(Encode, Decode)]
struct TracingMetadata {
    name: Vec<u8>,
    target: Vec<u8>,
    level: TracingLevel,
    file: Option<Vec<u8>>,
    line: Option<u32>,
	module_path: Option<Vec<u8>>,
	fields: Vec<Vec<u8>>,
	is_span: bool,
}

impl From<&Metadata<'_>> for TracingMetadata {
	fn from(m: &Metadata) -> TracingMetadata {
		TracingMetadata {
			name: m.name().as_bytes().into(),
			target: m.target().as_bytes().into(),
			module_path: m.module_path().map(|m| m.as_bytes().into()),
			file:  m.file().map(|m| m.as_bytes().into()),
			line: m.line().clone(),
			level: m.level().into(),
			fields: m.fields().iter().map(|f| f.name().as_bytes().into()).collect(),
			is_span: m.is_span(),
		}
	}
}


trait WasmTracingInterface {
	fn enabled(&self, metadata: &Metadata) -> bool;
	fn new_span(&self, span: TracingAttributes) -> Id;
	fn record(&self, span: &Id, values: &Record);
	fn event(&self, event: &Event);
	fn enter(&self, span: &Id);
	fn exit(&self, span: &Id);
}