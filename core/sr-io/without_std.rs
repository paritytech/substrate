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

use core::{intrinsics, panic::PanicInfo};

#[cfg(not(feature = "no_panic_handler"))]
#[panic_handler]
#[no_mangle]
pub fn panic(info: &PanicInfo) -> ! {
	unsafe {
		let message = rstd::alloc::format!("{}", info);
		misc::print_utf8(message.as_bytes());
		intrinsics::abort()
	}
}

#[cfg(not(feature = "no_oom"))]
#[alloc_error_handler]
pub extern fn oom(_: core::alloc::Layout) -> ! {
	static OOM_MSG: &str = "Runtime memory exhausted. Aborting";

	unsafe {
		misc::print_utf8(OOM_MSG.as_bytes());
		intrinsics::abort();
	}
}
