// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Custom panic hook with bug report link

use backtrace::Backtrace;
use std::io::{self, Write};
use std::panic::{self, PanicInfo};
use std::thread;

/// Set the panic hook
pub fn set() {
	panic::set_hook(Box::new(panic_hook));
}

static ABOUT_PANIC: &str = "
This is a bug. Please report it at:

    https://github.com/paritytech/polkadot/issues/new
";

fn panic_hook(info: &PanicInfo) {
	let location = info.location();
	let file = location.as_ref().map(|l| l.file()).unwrap_or("<unknown>");
	let line = location.as_ref().map(|l| l.line()).unwrap_or(0);

	let msg = match info.payload().downcast_ref::<&'static str>() {
		Some(s) => *s,
		None => match info.payload().downcast_ref::<String>() {
			Some(s) => &s[..],
			None => "Box<Any>",
		}
	};

	let thread = thread::current();
	let name = thread.name().unwrap_or("<unnamed>");

	let backtrace = Backtrace::new();

	let mut stderr = io::stderr();

	let _ = writeln!(stderr, "");
	let _ = writeln!(stderr, "====================");
	let _ = writeln!(stderr, "");
	let _ = writeln!(stderr, "{:?}", backtrace);
	let _ = writeln!(stderr, "");
	let _ = writeln!(
		stderr,
		"Thread '{}' panicked at '{}', {}:{}",
		name, msg, file, line
	);

	let _ = writeln!(stderr, "{}", ABOUT_PANIC);
	::std::process::exit(1);
}

