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

// tag::description[]
//! Safe global references to stack variables.
//!
//! Set up a global reference with environmental! macro giving it a name and type.
//! Use the `using` function scoped under its name to name a reference and call a function that
//! takes no parameters yet can access said reference through the similarly placed `with` function.
//!
//! # Examples
//!
//! ```
//! #[macro_use] extern crate environmental;
//! // create a place for the global reference to exist.
//! environmental!(counter: u32);
//! fn stuff() {
//!   // do some stuff, accessing the named reference as desired.
//!   counter::with(|i| *i += 1);
//! }
//! fn main() {
//!   // declare a stack variable of the same type as our global declaration.
//!   let mut counter_value = 41u32;
//!   // call stuff, setting up our `counter` environment as a reference to our counter_value var.
//!   counter::using(&mut counter_value, stuff);
//!   println!("The answer is {:?}", counter_value); // will print 42!
//!   stuff();	// safe! doesn't do anything.
//! }
//! ```
// end::description[]

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(const_fn))]

#[cfg(feature = "std")]
include!("../with_std.rs");

#[cfg(not(feature = "std"))]
include!("../without_std.rs");

#[doc(hidden)]
pub fn using<T: ?Sized, R, F: FnOnce() -> R>(
	global: &'static imp::LocalKey<imp::RefCell<Option<*mut T>>>,
	protected: &mut T,
	f: F
) -> R {
	// store the `protected` reference as a pointer so we can provide it to logic running within
	// `f`.
	// while we record this pointer (while it's non-zero) we guarantee:
	// - it will only be used once at any time (no reentrancy);
	// - that no other thread will use it; and
	// - that we do not use the original mutating reference while the pointer.
	// exists.
	global.with(|r| {
		let original = {
			let mut global = r.borrow_mut();
			imp::replace(&mut *global, Some(protected as _))
		};

		// even if `f` panics the original will be replaced.
		struct ReplaceOriginal<'a, T: 'a + ?Sized> {
			original: Option<*mut T>,
			global: &'a imp::RefCell<Option<*mut T>>,
		}

		impl<'a, T: 'a + ?Sized> Drop for ReplaceOriginal<'a, T> {
			fn drop(&mut self) {
				*self.global.borrow_mut() = self.original.take();
			}
		}

		let _guard = ReplaceOriginal {
			original,
			global: r,
		};

		f()
	})
}

#[doc(hidden)]
pub fn with<T: ?Sized, R, F: FnOnce(&mut T) -> R>(
	global: &'static imp::LocalKey<imp::RefCell<Option<*mut T>>>,
	mutator: F,
) -> Option<R> {
	global.with(|r| unsafe {
		let ptr = r.borrow_mut();
		match *ptr {
			Some(ptr) => {
				// safe because it's only non-zero when it's being called from using, which
				// is holding on to the underlying reference (and not using it itself) safely.
				Some(mutator(&mut *ptr))
			}
			None => None,
		}
	})
}

/// Declare a new global reference module whose underlying value does not contain references.
///
/// Will create a module of a given name that contains two functions:
///
/// * `pub fn using<R, F: FnOnce() -> R>(protected: &mut $t, f: F) -> R`
///   This executes `f`, returning its value. During the call, the module's reference is set to
///   be equal to `protected`.
/// * `pub fn with<R, F: FnOnce(&mut $t) -> R>(f: F) -> Option<R>`
///   This executes `f`, returning `Some` of its value if called from code that is being executed
///   as part of a `using` call. If not, it returns `None`. `f` is provided with one argument: the
///   same reference as provided to the most recent `using` call.
///
/// # Examples
///
/// Initializing the global context with a given value.
///
/// ```rust
/// #[macro_use] extern crate environmental;
/// environmental!(counter: u32);
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
///
/// Roughly the same, but with a trait object:
///
/// ```rust
/// #[macro_use] extern crate environmental;
///
/// trait Increment { fn increment(&mut self); }
///
/// impl Increment for i32 {
///	fn increment(&mut self) { *self += 1 }
/// }
///
/// environmental!(val: Increment + 'static);
///
/// fn main() {
///	let mut local = 0i32;
///	val::using(&mut local, || {
///		val::with(|v| for _ in 0..5 { v.increment() });
///	});
///
///	assert_eq!(local, 5);
/// }
/// ```
#[macro_export]
macro_rules! environmental {
	($name:ident : $t:ty) => {
		#[allow(non_camel_case_types)]
		struct $name { __private_field: () }

		thread_local_impl!(static GLOBAL: ::std::cell::RefCell<Option<*mut $t>>
			= ::std::cell::RefCell::new(None));

		impl $name {
			#[allow(unused_imports)]

			pub fn using<R, F: FnOnce() -> R>(
				protected: &mut $t,
				f: F
			) -> R {
				$crate::using(&GLOBAL, protected, f)
			}

			pub fn with<R, F: FnOnce(&mut $t) -> R>(
				f: F
			) -> Option<R> {
				$crate::with(&GLOBAL, |x| f(x))
			}
		}
	};
	($name:ident : trait @$t:ident [$($args:ty,)*]) => {
		#[allow(non_camel_case_types, dead_code)]
		struct $name { __private_field: () }

		thread_local_impl!(static GLOBAL: $crate::imp::RefCell<Option<*mut ($t<$($args),*> + 'static)>>
			= $crate::imp::RefCell::new(None));

		impl $name {
		#[allow(unused_imports)]

			pub fn using<R, F: FnOnce() -> R>(
				protected: &mut $t<$($args),*>,
				f: F
			) -> R {
				let lifetime_extended = unsafe {
					$crate::imp::transmute::<&mut $t<$($args),*>, &mut ($t<$($args),*> + 'static)>(protected)
				};
				$crate::using(&GLOBAL, lifetime_extended, f)
			}

			pub fn with<R, F: for<'a> FnOnce(&'a mut ($t<$($args),*> + 'a)) -> R>(
				f: F
			) -> Option<R> {
				$crate::with(&GLOBAL, |x| f(x))
			}
		}
	};
	($name:ident<$traittype:ident> : trait $t:ident <$concretetype:ty>) => {
		#[allow(non_camel_case_types, dead_code)]
		struct $name <H: $traittype> { _private_field: $crate::imp::PhantomData<H> }

		thread_local_impl!(static GLOBAL: $crate::imp::RefCell<Option<*mut ($t<$concretetype> + 'static)>>
			= $crate::imp::RefCell::new(None));

		impl<H: $traittype> $name<H> {
			#[allow(unused_imports)]
			pub fn using<R, F: FnOnce() -> R>(
				protected: &mut $t<H>,
				f: F
			) -> R {
				let lifetime_extended = unsafe {
					$crate::imp::transmute::<&mut $t<H>, &mut ($t<$concretetype> + 'static)>(protected)
				};
				$crate::using(&GLOBAL, lifetime_extended, f)
			}

			pub fn with<R, F: for<'a> FnOnce(&'a mut ($t<$concretetype> + 'a)) -> R>(
				f: F
			) -> Option<R> {
				$crate::with(&GLOBAL, |x| f(x))
			}
		}
	};
	($name:ident : trait $t:ident <>) => { environmental! { $name : trait @$t [] } };
	($name:ident : trait $t:ident < $($args:ty),* $(,)* >) => { environmental! { $name : trait @$t [$($args,)*] } };
	($name:ident : trait $t:ident) => { environmental! { $name : trait @$t [] } };
}

#[cfg(test)]
mod tests {

	#[test]
	fn simple_works() {
		environmental!(counter: u32);

		fn stuff() { counter::with(|value| *value += 1); };

		// declare a stack variable of the same type as our global declaration.
		let mut local = 41u32;

		// call stuff, setting up our `counter` environment as a reference to our local counter var.
		counter::using(&mut local, stuff);
		assert_eq!(local, 42);
		stuff();	// safe! doesn't do anything.
		assert_eq!(local, 42);
	}

	#[test]
	fn overwrite_with_lesser_lifetime() {
		environmental!(items: Vec<u8>);

		let mut local_items = vec![1, 2, 3];
		items::using(&mut local_items, || {
			let dies_at_end = vec![4, 5, 6];
			items::with(|items| *items = dies_at_end);
		});

		assert_eq!(local_items, vec![4, 5, 6]);
	}

	#[test]
	fn declare_with_trait_object() {
		trait Foo {
			fn get(&self) -> i32;
			fn set(&mut self, x: i32);
		}

		impl Foo for i32 {
			fn get(&self) -> i32 { *self }
			fn set(&mut self, x: i32) { *self = x }
		}

		environmental!(foo: Foo + 'static);

		fn stuff() {
			foo::with(|value| {
				let new_val = value.get() + 1;
				value.set(new_val);
			});
		}

		let mut local = 41i32;
		foo::using(&mut local, stuff);

		assert_eq!(local, 42);

		stuff(); // doesn't do anything.

		assert_eq!(local, 42);
	}

	#[test]
	fn unwind_recursive() {
		use std::panic;

		environmental!(items: Vec<u8>);

		let panicked = panic::catch_unwind(|| {
			let mut local_outer = vec![1, 2, 3];

			items::using(&mut local_outer, || {
				let mut local_inner = vec![4, 5, 6];
				items::using(&mut local_inner, || {
					panic!("are you unsafe?");
				})
			});
		}).is_err();

		assert!(panicked);

		let mut was_cleared = true;
		items::with(|_items| was_cleared = false);

		assert!(was_cleared);
	}

	#[test]
	fn use_non_static_trait() {
		trait Sum { fn sum(&self) -> usize; }
		impl<'a> Sum for &'a [usize] {
			fn sum(&self) -> usize {
				self.iter().fold(0, |a, c| a + c)
			}
		}

		environmental!(sum: trait Sum);
		let numbers = vec![1, 2, 3, 4, 5];
		let mut numbers = &numbers[..];
		let got_sum = sum::using(&mut numbers, || {
			sum::with(|x| x.sum())
		}).unwrap();

		assert_eq!(got_sum, 15);
	}

	#[test]
	fn use_generic_trait() {
		trait Plus { fn plus42() -> usize; }
		struct ConcretePlus;
		impl Plus for ConcretePlus {
			fn plus42() -> usize { 42 }
		}
		trait Multiplier<T: Plus> { fn mul_and_add(&self) -> usize; }
		impl<'a, P: Plus> Multiplier<P> for &'a [usize] {
			fn mul_and_add(&self) -> usize {
				self.iter().fold(1, |a, c| a * c) + P::plus42()
			}
		}

		let numbers = vec![1, 2, 3];
		let mut numbers = &numbers[..];
		let out = foo::<ConcretePlus>::using(&mut numbers, || {
			foo::<ConcretePlus>::with(|x| x.mul_and_add() )
		}).unwrap();

		assert_eq!(out, 6 + 42);
		environmental!(foo<Plus>: trait Multiplier<ConcretePlus>);
	}
}
