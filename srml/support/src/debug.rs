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

use rstd::prelude::Vec;
use rstd::collections::btree_map::BTreeMap;
use rstd::fmt::{self, Write, Debug};

pub use log::{info, debug, error, trace, warn};

#[cfg(feature = "std")]
pub mod native {
	pub use super::{info, debug, error, trace, warn, print};
}
#[cfg(not(feature = "std"))]
pub mod native {
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

macro_rules! print {
	($($arg:tt)+) => {
		let mut w = $crate::debug::Writer::default();
		let _ = core::write!(&mut w, $($arg)+);
		w.print();
	}
}

/// Print out the debuggable type.
pub fn debug(data: &impl Debug) {
	print!("{:?}", data);
}

#[derive(Default)]
pub struct Writer(Vec<u8>);

impl Write for Writer {
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

pub struct RuntimeLogger {
	level: log::LevelFilter,
	filters: BTreeMap<Vec<u8>, log::LevelFilter>,
}

impl log::Log for RuntimeLogger {
	fn enabled(&self, metadata: &log::Metadata) -> bool {
		let level = metadata.level();

		// target-specific filter
		if let Some(f) = self.filters.get(metadata.target().as_bytes()) {
			return f <= &level
		}

		// general filter
		self.level <= level
	}

	fn log(&self, record: &log::Record) {
		if !self.enabled(record.metadata()) {
			return;
		}

		print!(
			"{}:{} -- {}",
			record.level(),
			record.target(),
			record.args(),
		);
	}

	fn flush(&self) {}
}
