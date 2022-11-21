// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Contains the [`crate::defer!`] macro for *deferring* the execution
//! of code until the current scope is dropped.
//! This helps with *always* executing cleanup code.

/// Executes the wrapped closure on drop.
///
/// Should be used together with the [`crate::defer!`] macro.
#[must_use]
pub struct DeferGuard<F: FnOnce()>(pub Option<F>);

impl<F: FnOnce()> Drop for DeferGuard<F> {
	fn drop(&mut self) {
		self.0.take().map(|f| f());
	}
}

/// Executes the given code when the current scope is dropped.
///
/// Multiple calls to [`crate::defer!`] will execute the passed codes in reverse order.
/// This also applies to panic stack unwinding.
///
/// # Example
///
/// ```rust
/// use sp_core::defer;
///
/// let message = std::cell::RefCell::new("".to_string());
/// {
/// 	defer!(
/// 		message.borrow_mut().push_str("world!");
/// 	);
/// 	defer!(
/// 		message.borrow_mut().push_str("Hello ");
/// 	);
/// }
/// assert_eq!(*message.borrow(), "Hello world!");
/// ```
#[macro_export]
macro_rules! defer(
	( $( $code:tt )* ) => {
		let _guard = $crate::defer::DeferGuard(Some(|| { $( $code )* }));
	};
);

#[cfg(test)]
mod test {
	#[test]
	fn defer_guard_works() {
		let mut called = false;
		{
			defer!(
				called = true;
			);
		}
		assert!(called, "DeferGuard should have executed the closure");
	}

	#[test]
	/// `defer` executes the code in reverse order of being called.
	fn defer_guard_order_works() {
		let called = std::cell::RefCell::new(1);

		defer!(
			assert_eq!(*called.borrow(), 3);
		);
		defer!(
			assert_eq!(*called.borrow(), 2);
			*called.borrow_mut() = 3;
		);
		defer!({
			assert_eq!(*called.borrow(), 1);
			*called.borrow_mut() = 2;
		});
	}

	#[test]
	#[allow(unused_braces)]
	#[allow(clippy::unnecessary_operation)]
	fn defer_guard_syntax_works() {
		let called = std::cell::RefCell::new(0);
		{
			defer!(*called.borrow_mut() += 1);
			defer!(*called.borrow_mut() += 1;); // With ;
			defer!({ *called.borrow_mut() += 1 });
			defer!({ *called.borrow_mut() += 1 };); // With ;
		}
		assert_eq!(*called.borrow(), 4);
	}

	#[test]
	/// `defer` executes the code even in case of a panic.
	fn defer_guard_panic_unwind_works() {
		use std::panic::{catch_unwind, AssertUnwindSafe};
		let mut called = false;

		let should_panic = catch_unwind(AssertUnwindSafe(|| {
			defer!(called = true);
			panic!();
		}));

		assert!(should_panic.is_err(), "DeferGuard should have panicked");
		assert!(called, "DeferGuard should have executed the closure");
	}

	#[test]
	/// `defer` executes the code even in case another `defer` panics.
	fn defer_guard_defer_panics_unwind_works() {
		use std::panic::{catch_unwind, AssertUnwindSafe};
		let counter = std::cell::RefCell::new(0);

		let should_panic = catch_unwind(AssertUnwindSafe(|| {
			defer!(*counter.borrow_mut() += 1);
			defer!(
				*counter.borrow_mut() += 1;
				panic!();
			);
			defer!(*counter.borrow_mut() += 1);
		}));

		assert!(should_panic.is_err(), "DeferGuard should have panicked");
		assert_eq!(*counter.borrow(), 3, "DeferGuard should have executed the closure");
	}
}
