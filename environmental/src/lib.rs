// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

use std::cell::RefCell;
use std::thread::LocalKey;

pub fn using_environment<'a, T: 'a, S, F: FnOnce()>(
	global: &'static LocalKey<RefCell<*mut S>>,
	protected: &'a mut T,
	f: F
) {
	global.with(|r| *r.borrow_mut() = protected as *mut T as *mut S);
	f();
	global.with(|r| *r.borrow_mut() = 0 as *mut S);
}

pub fn with_environment<'r, R, S, T: 'r, F: FnOnce(&'r mut T) -> R>(
	global: &'static LocalKey<RefCell<*mut S>>,
	mutator: F,
) -> Option<R> {

	global.with(|r| {
		let br = r.borrow_mut();
		if *br != 0 as *mut S {
			// safe because it's only non-zero when it in with_environment, which
			// is holding on to the underlying reference safely
			unsafe {
				Some(mutator(&mut *(*br as *mut S as *mut T)))
			}
		} else {
			None
		}
	})
}

#[macro_export]
macro_rules! decl_environment {
	($name:ident : $t:ty) => {
		thread_local! {
			static $name: std::cell::RefCell<*mut $t> = std::cell::RefCell::new(0 as *mut $t);
		}
	}
}

#[macro_export]
macro_rules! declare_generic_environment {
	($name:ident : $t:tt) => {
		mod $name {
			use super::*;

			decl_environment!(GLOBAL: $t<'static> );

			pub fn using<'a: 'b, 'b, F: FnOnce(), T: 'a>(protected: &'b mut T, f: F) {
				$crate::using_environment(&GLOBAL, protected, f);
			}

			pub fn with<R, F: for<'r, 't: 'r> FnOnce(&'r mut $t<'t>) -> R>(
				f: F
			) -> Option<R> {
				let dummy = ();
				with_closed(f, &dummy)
			}

			fn with_closed<'d: 't, 't: 'r, 'r, R, F: FnOnce(&'r mut $t<'t>) -> R>(
				f: F,
				_dummy: &'d (),
			) -> Option<R> {
				$crate::with_environment(&GLOBAL, f)
			}
		}
	}
}

#[macro_export]
macro_rules! declare_simple_environment {
	($name:ident : $t:tt) => {
		mod $name {
			use super::*;

			decl_environment!(GLOBAL: $t );

			pub fn using<'a: 'b, 'b, F: FnOnce(), T: 'a>(protected: &'b mut T, f: F) {
				$crate::using_environment(&GLOBAL, protected, f);
			}

			pub fn with<R, F: for<'r> FnOnce(&'r mut $t -> R)>(
				f: F
			) -> Option<R> {
				let dummy = ();
				with_closed(f, &dummy)
			}

			fn with_closed<'d: 'r, 'r, R, F: FnOnce(&'r mut $t -> R)>(
				f: F,
				_dummy: &'d (),
			) -> Option<R> {
				$crate::with_environment(&GLOBAL, f)
			}
		}
	}
}
