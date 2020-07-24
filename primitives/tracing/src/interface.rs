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
	metadata::{Metadata, Kind},
	field::{Field, Visit},
	event::{Event},
	span::{
		Attributes,
		Id,
		Record,
	},
	Level,
};

use sp_std::vec::Vec;
use sp_runtime_interface::runtime_interface;


#[derive(Encode, Decode, Debug)]
pub enum FieldValue {
	I64(i64),
	U64(u64),
	Bool(bool),
	Str(Vec<u8>),
	Debug(Vec<u8>),
}


#[derive(Encode, Decode, Debug)]
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
pub struct WasmTracingAttributes {
	pub parent_id: Option<u64>,
	pub fields: Fields
}

impl From<&Attributes<'_>> for WasmTracingAttributes {
	fn from(a: &Attributes) -> WasmTracingAttributes {
		let mut fields = Fields(Vec::new());
		a.record(&mut fields);
		WasmTracingAttributes {
			parent_id: a.parent().map(|a| a.into_u64()),
			fields
		}
	}
}


#[derive(Encode, Decode)]
pub enum WasmTracingLevel {
	ERROR,
	WARN,
	INFO,
	DEBUG,
	TRACE
}

impl From<&Level> for WasmTracingLevel {
	fn from(lvl: &Level) -> WasmTracingLevel {
		match *lvl {
			Level::ERROR => WasmTracingLevel::ERROR,
			Level::WARN => WasmTracingLevel::WARN,
			Level::INFO => WasmTracingLevel::INFO,
			Level::DEBUG => WasmTracingLevel::DEBUG,
			Level::TRACE => WasmTracingLevel::TRACE,
		}
	}
}

impl Into<Level> for WasmTracingLevel {
	fn into(self) -> Level {
		match self {
			WasmTracingLevel::ERROR => Level::ERROR,
			WasmTracingLevel::WARN => Level::WARN,
			WasmTracingLevel::INFO => Level::INFO,
			WasmTracingLevel::DEBUG => Level::DEBUG,
			WasmTracingLevel::TRACE => Level::TRACE,
		}
	}
}

#[derive(Encode, Decode)]
pub struct WasmTracingMetadata {
    target: Vec<u8>,
    level: WasmTracingLevel,
    file: Option<Vec<u8>>,
    line: Option<u32>,
	module_path: Option<Vec<u8>>,
	is_span: bool,
}

impl From<&Metadata<'_>> for WasmTracingMetadata {
	fn from(m: &Metadata) -> WasmTracingMetadata {
		WasmTracingMetadata {
			target: m.target().as_bytes().into(),
			module_path: m.module_path().map(|m| m.as_bytes().into()),
			file:  m.file().map(|m| m.as_bytes().into()),
			line: m.line().clone(),
			level: m.level().into(),
			is_span: m.is_span(),
		}
	}
}

// #[cfg(feature="std")]
// impl<'a> Into<Metadata<'a>> for WasmTracingMetadata {
// 	fn into(self) -> Metadata<'a> {
// 		Metadata::new(
// 			"wasm_tracing", // must be static, it's the same for all then
// 			std::str::from_utf8(self.target.as_slice()).unwrap_or("<unknown>"),
// 			self.level.into(),
// 			self.file.as_ref().and_then(|s| std::str::from_utf8(s.as_slice()).ok()),
// 			self.line,
// 			self.module_path.as_ref().and_then(|s| std::str::from_utf8(s.as_slice()).ok()),
// 			Default::default(),
// 			if self.is_span { Kind::SPAN } else { Kind::EVENT } 
// 		)
// 	}
// }


#[derive(Encode, Decode)]
pub struct WasmTracingEvent;

#[derive(Encode, Decode)]
pub struct WasmTracingRecord;

pub trait TracingSubscriber {
	fn enabled(&self, metadata: WasmTracingMetadata) -> bool;
	fn new_span(&self, span: WasmTracingAttributes) -> u64;
	fn record(&self, span: u64, values: WasmTracingRecord);
	fn event(&self, event: WasmTracingEvent);
	fn enter(&self, span: u64);
	fn exit(&self, span: u64);
}

sp_externalities::decl_extension! {
	/// The keystore extension to register/retrieve from the externalities.
	pub struct WasmTracer(dyn TracingSubscriber + 'static + Send);
}


/// Interface that provides tracing functions
// #[runtime_interface(wasm_only, no_tracing)]
#[runtime_interface]
pub trait WasmTracing {
	fn enabled(&self, metadata: WasmTracingMetadata) -> bool {
		self.extension::<WasmTracer>().map(|t|{
			t.enabled(metadata)
		}).unwrap_or(false)
	}
	fn new_span(&self, span: WasmTracingAttributes) -> u64 {
		self.extension::<WasmTracer>().map(|t|{
			t.new_span(span)
		}).unwrap_or(0)
	}
	fn record(&self, span: u64, values: WasmTracingRecord) {
		self.extension::<WasmTracer>().map(|t|{
			t.record(span, values)
		});
	}
	fn event(&self, event: WasmTracingEvent) {
		self.extension::<WasmTracer>().map(|t|{
			t.event(event)
		});
	}
	fn enter(&self, span: u64) {
		self.extension::<WasmTracer>().map(|t|{
			t.enter(span)
		});
	}
	fn exit(&self, span: u64) {
		self.extension::<WasmTracer>().map(|t|{
			t.exit(span)
		});
	}
}