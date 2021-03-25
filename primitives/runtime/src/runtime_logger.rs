// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! A logger that can be used to log from the runtime.
//!
//! See [`RuntimeLogger`] for more docs.

/// Runtime logger implementation - `log` crate backend.
///
/// The logger should be initialized if you want to display
/// logs inside the runtime that is not necessarily running natively.
pub struct RuntimeLogger;

impl RuntimeLogger {
	/// Initialize the logger.
	///
	/// This is a no-op when running natively (`std`).
	#[cfg(feature = "std")]
	pub fn init() {}

	/// Initialize the logger.
	///
	/// This is a no-op when running natively (`std`).
	#[cfg(not(feature = "std"))]
	pub fn init() {
		static LOGGER: RuntimeLogger = RuntimeLogger;
		let _ = log::set_logger(&LOGGER);

		// Set max level to `TRACE` to ensure we propagate
		// all log entries to the native side that will do the
		// final filtering on what should be printed.
		//
		// If we don't set any level, logging is disabled
		// completly.
		log::set_max_level(log::LevelFilter::Trace);
	}
}

impl log::Log for RuntimeLogger {
	fn enabled(&self, _metadata: &log::Metadata) -> bool {
		// to avoid calling to host twice, we pass everything
		// and let the host decide what to print.
		// If someone is initializing the logger they should
		// know what they are doing.
		true
	}

	fn log(&self, record: &log::Record) {
		use sp_std::fmt::Write;
		let mut w = sp_std::Writer::default();
		let _ = ::core::write!(&mut w, "{}", record.args());

		sp_io::logging::log(
			record.level().into(),
			record.target(),
			w.inner(),
		);
	}

	fn flush(&self) {}
}

#[cfg(test)]
mod tests {
	use substrate_test_runtime_client::{
		ExecutionStrategy, TestClientBuilderExt, DefaultTestClientBuilderExt,
		TestClientBuilder, runtime::TestAPI,
	};
	use sp_api::{ProvideRuntimeApi, BlockId};

	#[test]
	fn ensure_runtime_logger_works() {
		if std::env::var("RUN_TEST").is_ok() {
			sp_tracing::try_init_simple();

			let client = TestClientBuilder::new()
				.set_execution_strategy(ExecutionStrategy::AlwaysWasm).build();
			let runtime_api = client.runtime_api();
			let block_id = BlockId::Number(0);
			runtime_api.do_trace_log(&block_id).expect("Logging should not fail");
		} else {
			let executable = std::env::current_exe().unwrap();
			let output = std::process::Command::new(executable)
				.env("RUN_TEST", "1")
				.env("RUST_LOG", "trace")
				.args(&["--nocapture", "ensure_runtime_logger_works"])
				.output()
				.unwrap();

			let output = dbg!(String::from_utf8(output.stderr).unwrap());
			assert!(output.contains("Hey I'm runtime"));
		}
	}
}
