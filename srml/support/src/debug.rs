// Copyright 2019 Parity Technologies (UK) Ltd.
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

use rstd::vec::Vec;
use rstd::fmt::{self, Debug};

pub use log::{info, debug, error, trace, warn};

// TODO [ToDr] Docs!!!

#[cfg(feature = "std")]
pub mod native {
	pub use super::{info, debug, error, trace, warn};
	pub use crate::runtime_print;
}
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
	pub use noop as runtime_print;
}

#[macro_export]
macro_rules! runtime_print {
	($($arg:tt)+) => {
		use core::fmt::Write;
		let mut w = $crate::debug::Writer::default();
		let _ = core::write!(&mut w, $($arg)+);
		w.print();
	}
}

/// Print out the debuggable type.
pub fn debug(data: &impl Debug) {
	runtime_print!("{:?}", data);
}

#[derive(Default)]
pub struct Writer(Vec<u8>);

impl fmt::Write for Writer {
	fn write_str(&mut self, s: &str) -> fmt::Result {
		self.0.extend(s.as_bytes());
		Ok(())
	}
}

impl Writer {
	/// Print the content of this writer out.
	pub fn print(&self) {
		runtime_io::print_utf8(&self.0)
	}
}

pub struct RuntimeLogger;

impl RuntimeLogger {
	#[cfg(feature = "std")]
	pub fn init() {}

	#[cfg(not(feature = "std"))]
	pub fn init() {
		static LOGGER: RuntimeLogger = RuntimeLogger;;
		let _ = log::set_logger(&LOGGER);
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
		let mut w = Writer::default();
		let _ = core::write!(&mut w, "{}", record.args());

		runtime_io::log(
			record.level().into(),
			record.target().as_bytes(),
			&w.0,
		);
	}

	fn flush(&self) {}
}
