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

// #![cfg_attr(not(feature = "std"), no_std)]
// //! Proxy to allow entering tracing spans from wasm.
// use core::{
// 	default::Default,
// 	fmt::Debug,
// };

// use codec::{Encode, Decode};
use crate::{
	WasmMetadata, WasmAttributes, WasmRecord, WasmEvent
};
//
// #[cfg(feature = "std")]
// use sp_externalities::{ExternalitiesExt, Externalities};

// use sp_runtime_interface::runtime_interface;

pub trait TracingSubscriber: Send + Sync {
	fn enabled(&self, metadata: WasmMetadata) -> bool;
	fn new_span(&self, attrs: WasmAttributes) -> u64;
	fn record(&self, span: u64, values: WasmRecord);
	fn event(&self, event: WasmEvent);
	fn enter(&self, span: u64);
	fn exit(&self, span: u64);
}
//
// #[cfg(feature="std")]
// sp_externalities::decl_extension! {
// 	/// The keystore extension to register/retrieve from the externalities.
// 	pub struct WasmTracer(Box<dyn TracingSubscriber + 'static + Send + Sync>);
// }
//
//
// /// Interface that provides tracing functions
// // #[runtime_interface(wasm_only, no_tracing)]
// #[runtime_interface]
// pub trait WasmTracing {
// 	fn enabled(&mut self, metadata: WasmMetadata) -> bool {
// 		self.extension::<WasmTracer>().map(|t|{
// 			t.0.enabled(metadata)
// 		}).unwrap_or(false)
// 	}
// 	fn new_span(&mut self, span: WasmAttributes) -> u64 {
// 		self.extension::<WasmTracer>().map(|t|{
// 			t.0.new_span(span)
// 		}).unwrap_or(0)
// 	}
// 	fn record(&mut self, span: u64, values: WasmRecord) {
// 		self.extension::<WasmTracer>().map(|t|{
// 			t.0.record(span, values)
// 		});
// 	}
// 	fn event(&mut self, event: WasmEvent) {
// 		self.extension::<WasmTracer>().map(|t|{
// 			t.0.event(event)
// 		});
// 	}
// 	fn enter(&mut self, span: u64) {
// 		self.extension::<WasmTracer>().map(|t|{
// 			t.0.enter(span)
// 		});
// 	}
// 	fn exit(&mut self, span: u64) {
// 		self.extension::<WasmTracer>().map(|t|{
// 			t.0.exit(span)
// 		});
// 	}
// }