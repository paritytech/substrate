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

//! Safe global references to stack variables.
//!
//! Set up a global reference with declare_simple! macro giving it a name and type.
//! Use the `using` function scoped under its name to name a reference and call a function that
//! takes no parameters yet can access said reference through the similarly placed `with` function.
//!
//! # Examples
//!
//! ```
//! #[macro_use] extern crate environmental;
//! // create a place for the global reference to exist.
//! declare_simple!(counter: u32);
//! fn stuff() {
//!   // do some stuff, accessing the named reference as desired.
//!   counter::with(|i| *i += 1);
//! }
//! fn main() {
//!   // declare a stack variable of the same type as our global declaration.
//!   let mut counter_value = 41u32;
//!   // call stuff, setting up our `counter` environment as a refrence to our counter_value var.
//!   counter::using(&mut counter_value, stuff);
//!   println!("The answer is {:?}", counter_value); // will print 42!
//!   stuff();	// safe! doesn't do anything.
//! }
//! ```

#[doc(hidden)]
pub use std::cell::RefCell;
use std::thread::LocalKey;

#[doc(hidden)]
pub fn using<'a, T: 'a, R, S, F: FnOnce() -> R>(
	global: &'static LocalKey<RefCell<*mut S>>,
	protected: &'a mut T,
	f: F
) -> R {
	// store the `protected` reference as a pointer so we can provide it to logic running within
	// `f`.
	// while we record this pointer (while it's non-zero) we guarantee:
	// - it will only be used once at any time (no reentrancy);
	// - that no other thread will use it; and
	// - that we do not use the original mutating reference while the pointer.
	// exists.
	let original = global.with(|r| {
		let mut b = r.borrow_mut();
		let o = *b;
		*b = protected as *mut T as *mut S;
		o
	});
	let r = f();
	global.with(|r| *r.borrow_mut() = original);
	r
}

#[doc(hidden)]
pub fn with<'r, R, S, T: 'r, F: FnOnce(&'r mut T) -> R>(
	global: &'static LocalKey<RefCell<*mut S>>,
	mutator: F,
) -> Option<R> {
	global.with(|r| {
		let br = r.borrow_mut();
		if *br != 0 as *mut S {
			// safe because it's only non-zero when it's being called from using, which
			// is holding on to the underlying reference (and not using it itself) safely.
			unsafe {
				Some(mutator(&mut *(*br as *mut S as *mut T)))
			}
		} else {
			None
		}
	})
}

#[doc(hidden)]
#[macro_export]
macro_rules! decl {
	($name:ident : $t:ty) => {
		thread_local! {
			static $name: $crate::RefCell<*mut $t> = $crate::RefCell::new(0 as *mut $t);
		}
	}
}

/// Declare a new global reference module whose underlying value does not contain references.
///
/// Will create a module of a given name that contains two functions:
/// * `pub fn using<'a: 'b, 'b, R, F: FnOnce() -> R, T: 'a>(protected: &'b mut T, f: F) -> R`
///   This executes `f`, returning its value. During the call, the module's reference is set to
///   be equal to `protected`.
/// * `pub fn with<R, F: for<'r, 't: 'r> FnOnce(&'r mut $t<'t>) -> R>(f: F) -> Option<R>`
///   This executes `f`, returning `Some` of its value if called from code that is being executed
///   as part of a `using` call. If not, it returns `None`. `f` is provided with one argument: the
///   same reference as provided to the most recent `using` call.
///
/// # Examples
///
/// ```
/// #[macro_use] extern crate environmental;
/// declare_simple!(counter: u32);
/// fn main() {
///   let mut counter_value = 41u32;
///   counter::using(&mut counter_value, || {
///     let odd = counter::with(|value|
///       if *value % 2 == 1 {
///         *value += 1; true
///       } else {
///         *value -= 3; false
///       }).unwrap();	// safe because we're inside a counter::using
///     println!("counter was {}", match odd { true => "odd", _ => "even" });
///   });
///
///   println!("The answer is {:?}", counter_value); // 42
/// }
/// ```
#[macro_export]
macro_rules! declare_simple {
	($name:ident : $t:tt) => {
		mod $name {
			#[allow(unused_imports)]
			use super::*;

			decl!(GLOBAL: $t);

			pub fn using<'a: 'b, 'b, R, F: FnOnce() -> R, T: 'a>(
				protected: &'b mut T,
				f: F
			) -> R {
				$crate::using(&GLOBAL, protected, f)
			}

			pub fn with<R, F: for<'r> FnOnce(&'r mut $t) -> R>(
				f: F
			) -> Option<R> {
				let dummy = ();
				with_closed(f, &dummy)
			}

			fn with_closed<'d: 'r, 'r, R, F: FnOnce(&'r mut $t) -> R>(
				f: F,
				_dummy: &'d (),
			) -> Option<R> {
				$crate::with(&GLOBAL, f)
			}
		}
	}
}

/// Declare a new global reference module whose underlying value is generic over a reference.
///
/// Will create a module of a given name that contains two functions:
///
/// * `pub fn using<'a: 'b, 'b, R, F: FnOnce() -> R, T: 'a>(protected: &'b mut T, f: F) -> R`
///   This executes `f`, returning its value. During the call, the module's reference is set to
///   be equal to `protected`.
/// * `pub fn with<R, F: for<'r, 't: 'r> FnOnce(&'r mut $t<'t>) -> R>(f: F) -> Option<R>`
///   This executes `f`, returning `Some` of its value if called from code that is being executed
///   as part of a `using` call. If not, it returns `None`. `f` is provided with one argument: the
///   same reference as provided to the most recent `using` call.
///
/// # Examples
///
/// ```
/// #[macro_use] extern crate environmental;
/// // a type that we want to reference from a temp global; it has a reference in it.
/// struct WithReference<'a> { answer_ref: &'a mut u32, }
/// // create a place for the global reference to exist.
/// declare_generic!(counter: WithReference);
/// fn stuff() {
///   // do some stuff, accessing the named reference as desired.
///   counter::with(|i| *i.answer_ref += 1);
/// }
/// fn main() {
///   // declare a stack variable of the same type as our global declaration.
///   let mut answer = 41u32;
///   {
///     let mut ref_struct = WithReference { answer_ref: &mut answer, };
///     counter::using(&mut ref_struct, stuff);
///   }
///   println!("The answer is {:?}", answer); // will print 42!
/// }
/// ```
#[macro_export]
macro_rules! declare_generic {
	($name:ident : $t:tt) => {
		mod $name {
			#[allow(unused_imports)]
			use super::*;

			decl!(GLOBAL: $t<'static> );

			pub fn using<'a: 'b, 'b, R, F: FnOnce() -> R, T: 'a>(
				protected: &'b mut T,
				f: F
			) -> R {
				$crate::using(&GLOBAL, protected, f)
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
				$crate::with(&GLOBAL, f)
			}
		}
	}
}

#[cfg(test)]
mod tests {
	declare_simple!(counter: u32);

	fn stuff() {
		// do some stuff, accessing the named reference as desired.
		counter::with(|value| *value += 1);
	}

	#[test]
	fn simple_works() {
		// declare a stack variable of the same type as our global declaration.
		let mut local = 41u32;
		// call stuff, setting up our `counter` environment as a refrence to our local counter var.
		counter::using(&mut local, stuff);
		println!("The answer is {:?}", local); // will print 42!
		stuff();	// safe! doesn't do anything.
	}
}
