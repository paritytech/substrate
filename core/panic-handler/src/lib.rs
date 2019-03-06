// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use std::cell::Cell;
use std::thread;

thread_local! {
	pub static ABORT: Cell<bool> = Cell::new(true);
}

/// Set the panic hook
pub fn set(bug_url: &'static str) {
	panic::set_hook(Box::new(move |c| panic_hook(c, bug_url)));
}

macro_rules! ABOUT_PANIC {
	() => ("
This is a bug. Please report it at:

	{}
")}

/// Set aborting flag. Returns previous value of the flag.
pub fn set_abort(enabled: bool) -> bool {
	ABORT.with(|flag| {
		let prev = flag.get();
		flag.set(enabled);
		prev
	})
}

/// Abort flag guard. Sets abort on construction and reverts to previous setting when dropped.
pub struct AbortGuard(bool);

impl AbortGuard {
	/// Create a new guard and set abort flag to specified value.
	pub fn new(enable: bool) -> AbortGuard {
		AbortGuard(set_abort(enable))
	}
}

impl Drop for AbortGuard {
	fn drop(&mut self) {
		set_abort(self.0);
	}
}

fn panic_hook(info: &PanicInfo, report_url: &'static str) {
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

	let _ = writeln!(stderr, ABOUT_PANIC!(), report_url);
	ABORT.with(|flag| {
		if flag.get() {
			::std::process::exit(1);
		}
	})
}

#[test]
fn does_not_abort() {
	set("test");
	let _guard = AbortGuard::new(false);
	::std::panic::catch_unwind(|| panic!()).ok();
}
