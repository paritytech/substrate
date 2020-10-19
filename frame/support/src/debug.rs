// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Runtime debugging and logging utilities.
//!
//! This module contains macros and functions that will allow
//! you to print logs out of the runtime code.
//!
//! First and foremost be aware that adding regular logging code to
//! your runtime will have a negative effect on the performance
//! and size of the blob. Luckily there are some ways to mitigate
//! this that are described below.
//!
//! First component to utilize debug-printing and logging is actually
//! located in `primitives` crate: `sp_core::RuntimeDebug`.
//! This custom-derive generates `core::fmt::Debug` implementation,
//! just like regular `derive(Debug)`, however it does not generate
//! any code when the code is compiled to WASM. This means that
//! you can safely sprinkle `RuntimeDebug` in your runtime codebase,
//! without affecting the size. This also allows you to print/log
//! both when the code is running natively or in WASM, but note
//! that WASM debug formatting of structs will be empty.
//!
//! ```rust,no_run
//!	use frame_support::debug;
//!
//! #[derive(sp_core::RuntimeDebug)]
//!	struct MyStruct {
//!   a: u64,
//!	}
//!
//! // First initialize the logger.
//! //
//! // This is only required when you want the logs to be printed
//! // also during non-native run.
//! // Note that enabling the logger has performance impact on
//! // WASM runtime execution and should be used sparingly.
//!	debug::RuntimeLogger::init();
//!
//! let x = MyStruct { a: 5 };
//!	// will log an info line `"My struct: MyStruct{a:5}"` when running
//!	// natively, but will only print `"My struct: "` when running WASM.
//!	debug::info!("My struct: {:?}", x);
//!
//!	// same output here, although this will print to stdout
//!	// (and without log format)
//!	debug::print!("My struct: {:?}", x);
//! ```
//!
//! If you want to avoid extra overhead in WASM, but still be able
//! to print / log when the code is executed natively you can use
//! macros coming from `native` sub-module. This module enables
//! logs conditionally and strips out logs in WASM.
//!
//! ```rust,no_run
//!	use frame_support::debug::native;
//!
//! #[derive(sp_core::RuntimeDebug)]
//!	struct MyStruct {
//!   a: u64,
//!	}
//!
//! // We don't initialize the logger, since
//! // we are not printing anything out in WASM.
//!	// debug::RuntimeLogger::init();
//!
//! let x = MyStruct { a: 5 };
//!
//!	// Displays an info log when running natively, nothing when WASM.
//!	native::info!("My struct: {:?}", x);
//!
//!	// same output to stdout, no overhead on WASM.
//!	native::print!("My struct: {:?}", x);
//! ```

use sp_std::fmt::{self, Debug};

pub use log::{info, debug, error, trace, warn};
pub use crate::runtime_print as print;
pub use sp_std::Writer;

/// Native-only logging.
///
/// Using any functions from this module will have any effect
/// only if the runtime is running natively (i.e. not via WASM)
#[cfg(feature = "std")]
pub mod native {
	pub use super::{info, debug, error, trace, warn, print};
}

/// Native-only logging.
///
/// Using any functions from this module will have any effect
/// only if the runtime is running natively (i.e. not via WASM)
#[cfg(not(feature = "std"))]
pub mod native {
	#[macro_export]
	macro_rules! noop {
		($($arg:tt)+) => {}
	}
	pub use noop as info;
	pub use noop as debug;
	pub use noop as error;
	pub use noop as trace;
	pub use noop as warn;
	pub use noop as print;
}

/// Print out a formatted message.
///
/// # Example
///
/// ```
/// frame_support::runtime_print!("my value is {}", 3);
/// ```
#[macro_export]
macro_rules! runtime_print {
	($($arg:tt)+) => {
		{
			use core::fmt::Write;
			let mut w = $crate::sp_std::Writer::default();
			let _ = core::write!(&mut w, $($arg)+);
			sp_io::misc::print_utf8(&w.inner())
		}
	}
}

/// Print out the debuggable type.
pub fn debug(data: &impl Debug) {
	runtime_print!("{:?}", data);
}

/// Runtime logger implementation - `log` crate backend.
///
/// The logger should be initialized if you want to display
/// logs inside the runtime that is not necessarily running natively.
///
/// When runtime is executed natively any log statements are displayed
/// even if this logger is NOT initialized.
///
/// Note that even though the logs are not displayed in WASM, they
/// may still affect the size and performance of the generated runtime.
/// To lower the footprint make sure to only use macros from `native`
/// sub-module.
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
		use fmt::Write;
		let mut w = sp_std::Writer::default();
		let _ = core::write!(&mut w, "{}", record.args());

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
	use sp_api::ProvideRuntimeApi;
	use sp_runtime::generic::BlockId;

	#[test]
	fn ensure_runtime_logger_works() {
		let executable = std::env::current_exe().unwrap();
		let output = std::process::Command::new(executable)
			.env("RUN_TEST", "1")
			.env("RUST_LOG", "trace")
			.args(&["--nocapture", "ensure_runtime_logger_works_implementation"])
			.output()
			.unwrap();

		let output = dbg!(String::from_utf8(output.stderr).unwrap());
		assert!(output.contains("Hey I'm runtime"));
	}

	/// This is no actual test. It will be called by `ensure_runtime_logger_works`
	/// to check that the runtime can print from the wasm side using the
	/// `RuntimeLogger`.
	#[test]
	fn ensure_runtime_logger_works_implementation() {
		if std::env::var("RUN_TEST").is_ok() {
			sp_tracing::try_init_simple();

			let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::AlwaysWasm).build();
			let runtime_api = client.runtime_api();
			let block_id = BlockId::Number(0);
			runtime_api.do_trace_log(&block_id).expect("Logging should not fail");
		}
	}
}
