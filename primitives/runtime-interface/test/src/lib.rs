// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Integration tests for runtime interface primitives
#![cfg(test)]

#![cfg(test)]

use sp_runtime_interface::*;

use sp_runtime_interface_test_wasm::{WASM_BINARY, test_api::HostFunctions};
use sp_runtime_interface_test_wasm_deprecated::WASM_BINARY as WASM_BINARY_DEPRECATED;

use sp_wasm_interface::HostFunctions as HostFunctionsT;
use sc_executor::CallInWasm;

use std::{collections::HashSet, sync::{Arc, Mutex}};

type TestExternalities = sp_state_machine::TestExternalities<sp_runtime::traits::BlakeTwo256, u64>;

fn call_wasm_method_with_result<HF: HostFunctionsT>(
	binary: &[u8],
	method: &str,
) -> Result<TestExternalities, String> {
	let mut ext = TestExternalities::default();
	let mut ext_ext = ext.ext();
	let mut host_functions = HF::host_functions();
	host_functions.extend(sp_io::SubstrateHostFunctions::host_functions());

	let executor = sc_executor::WasmExecutor::new(
		sc_executor::WasmExecutionMethod::Interpreted,
		Some(8),
		host_functions,
		8,
	);
	executor.call_in_wasm(
		binary,
		None,
		method,
		&[],
		&mut ext_ext,
		sp_core::traits::MissingHostFunctions::Disallow,
	).map_err(|e| format!("Failed to execute `{}`: {}", method, e))?;

	Ok(ext)
}

fn call_wasm_method<HF: HostFunctionsT>(binary: &[u8], method: &str) -> TestExternalities {
	call_wasm_method_with_result::<HF>(binary, method).unwrap()
}

#[test]
fn test_return_data() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_return_data");
}

#[test]
fn test_return_option_data() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_return_option_data");
}

#[test]
fn test_set_storage() {
	let mut ext = call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_set_storage");

	let expected = "world";
	assert_eq!(expected.as_bytes(), &ext.ext().storage("hello".as_bytes()).unwrap()[..]);
}

#[test]
fn test_return_value_into_mutable_reference() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_return_value_into_mutable_reference");
}

#[test]
fn test_get_and_return_array() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_get_and_return_array");
}

#[test]
fn test_array_as_mutable_reference() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_array_as_mutable_reference");
}

#[test]
fn test_return_input_public_key() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_return_input_public_key");
}

#[test]
fn host_function_not_found() {
	let err = call_wasm_method_with_result::<()>(&WASM_BINARY[..], "test_return_data").unwrap_err();

	assert!(err.contains("Instantiation: Export "));
	assert!(err.contains(" not found"));
}

#[test]
#[should_panic(expected = "Invalid utf8 data provided")]
fn test_invalid_utf8_data_should_return_an_error() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_invalid_utf8_data_should_return_an_error");
}

#[test]
fn test_overwrite_native_function_implementation() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_overwrite_native_function_implementation");
}

#[test]
fn test_u128_i128_as_parameter_and_return_value() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_u128_i128_as_parameter_and_return_value");
}

#[test]
fn test_vec_return_value_memory_is_freed() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_vec_return_value_memory_is_freed");
}

#[test]
fn test_encoded_return_value_memory_is_freed() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_encoded_return_value_memory_is_freed");
}

#[test]
fn test_array_return_value_memory_is_freed() {
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_array_return_value_memory_is_freed");
}

#[test]
fn test_versionining_with_new_host_works() {
	// We call to the new wasm binary with new host function.
	call_wasm_method::<HostFunctions>(
		&WASM_BINARY[..],
		"test_versionning_works",
	);

	// we call to the old wasm binary with a new host functions
	// old versions of host functions should be called and test should be ok!
	call_wasm_method::<HostFunctions>(
		&WASM_BINARY_DEPRECATED[..],
		"test_versionning_works",
	);
}

#[test]
fn test_tracing() {
	use tracing::span::Id as SpanId;

	#[derive(Clone)]
	struct TracingSubscriber(Arc<Mutex<Inner>>);

	#[derive(Default)]
	struct Inner {
		spans: HashSet<&'static str>,
	}

	impl tracing::subscriber::Subscriber for TracingSubscriber {
		fn enabled(&self, _: &tracing::Metadata) -> bool { true }

		fn new_span(&self, span: &tracing::span::Attributes) -> tracing::Id {
			let mut inner = self.0.lock().unwrap();
			let id = SpanId::from_u64((inner.spans.len() + 1) as _);
			inner.spans.insert(span.metadata().name());
			id
		}

		fn record(&self, _: &SpanId, _: &tracing::span::Record) {}

		fn record_follows_from(&self, _: &SpanId, _: &SpanId) {}

		fn event(&self, _: &tracing::Event) {}

		fn enter(&self, _: &SpanId) {}

		fn exit(&self, _: &SpanId) {}
	}

	let subscriber = TracingSubscriber(Default::default());
	let _guard = tracing::subscriber::set_default(subscriber.clone());

	// Call some method to generate a trace
	call_wasm_method::<HostFunctions>(&WASM_BINARY[..], "test_return_data");

	let inner = subscriber.0.lock().unwrap();
	assert!(inner.spans.contains("return_input_version_1"));
	assert!(inner.spans.contains("ext_test_api_return_input_version_1"));
}
