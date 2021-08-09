// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Traits and associated utilities for dealing with abstract constraint filters.

pub use super::members::Contains;
use sp_std::marker::PhantomData;

/// Trait to add a constraint onto the filter.
pub trait FilterStack<T>: Contains<T> {
	/// The type used to archive the stack.
	type Stack;

	/// Add a new `constraint` onto the filter.
	fn push(constraint: impl Fn(&T) -> bool + 'static);

	/// Removes the most recently pushed, and not-yet-popped, constraint from the filter.
	fn pop();

	/// Clear the filter, returning a value that may be used later to `restore` it.
	fn take() -> Self::Stack;

	/// Restore the filter from a previous `take` operation.
	fn restore(taken: Self::Stack);
}

/// Guard type for pushing a constraint to a `FilterStack` and popping when dropped.
pub struct FilterStackGuard<F: FilterStack<T>, T>(PhantomData<(F, T)>);

/// Guard type for clearing all pushed constraints from a `FilterStack` and reinstating them when
/// dropped.
pub struct ClearFilterGuard<F: FilterStack<T>, T>(Option<F::Stack>, PhantomData<T>);

impl<F: FilterStack<T>, T> FilterStackGuard<F, T> {
	/// Create a new instance, adding a new `constraint` onto the filter `T`, and popping it when
	/// this instance is dropped.
	pub fn new(constraint: impl Fn(&T) -> bool + 'static) -> Self {
		F::push(constraint);
		Self(PhantomData)
	}
}

impl<F: FilterStack<T>, T> Drop for FilterStackGuard<F, T> {
	fn drop(&mut self) {
		F::pop();
	}
}

impl<F: FilterStack<T>, T> ClearFilterGuard<F, T> {
	/// Create a new instance, adding a new `constraint` onto the filter `T`, and popping it when
	/// this instance is dropped.
	pub fn new() -> Self {
		Self(Some(F::take()), PhantomData)
	}
}

impl<F: FilterStack<T>, T> Drop for ClearFilterGuard<F, T> {
	fn drop(&mut self) {
		if let Some(taken) = self.0.take() {
			F::restore(taken);
		}
	}
}

/// Simple trait for providing a filter over a reference to some type, given an instance of itself.
pub trait InstanceFilter<T>: Sized + Send + Sync {
	/// Determine if a given value should be allowed through the filter (returns `true`) or not.
	fn filter(&self, _: &T) -> bool;

	/// Determines whether `self` matches at least everything that `_o` does.
	fn is_superset(&self, _o: &Self) -> bool {
		false
	}
}

impl<T> InstanceFilter<T> for () {
	fn filter(&self, _: &T) -> bool {
		true
	}
	fn is_superset(&self, _o: &Self) -> bool {
		true
	}
}

/// Re-expected for the macro.
#[doc(hidden)]
pub use sp_std::{
	boxed::Box,
	cell::RefCell,
	mem::{swap, take},
	vec::Vec,
};

#[macro_export]
macro_rules! impl_filter_stack {
	($target:ty, $base:ty, $call:ty, $module:ident) => {
		#[cfg(feature = "std")]
		mod $module {
			#[allow(unused_imports)]
			use super::*;
			use $crate::traits::filter::{swap, take, RefCell, Vec, Box, Contains, FilterStack};

			thread_local! {
				static FILTER: RefCell<Vec<Box<dyn Fn(&$call) -> bool + 'static>>> = RefCell::new(Vec::new());
			}

			impl Contains<$call> for $target {
				fn contains(call: &$call) -> bool {
					<$base>::contains(call) &&
						FILTER.with(|filter| filter.borrow().iter().all(|f| f(call)))
				}
			}

			impl FilterStack<$call> for $target {
				type Stack = Vec<Box<dyn Fn(&$call) -> bool + 'static>>;
				fn push(f: impl Fn(&$call) -> bool + 'static) {
					FILTER.with(|filter| filter.borrow_mut().push(Box::new(f)));
				}
				fn pop() {
					FILTER.with(|filter| filter.borrow_mut().pop());
				}
				fn take() -> Self::Stack {
					FILTER.with(|filter| take(filter.borrow_mut().as_mut()))
				}
				fn restore(mut s: Self::Stack) {
					FILTER.with(|filter| swap(filter.borrow_mut().as_mut(), &mut s));
				}
			}
		}

		#[cfg(not(feature = "std"))]
		mod $module {
			#[allow(unused_imports)]
			use super::*;
			use $crate::traits::{swap, take, RefCell, Vec, Box, Contains, FilterStack};

			struct ThisFilter(RefCell<Vec<Box<dyn Fn(&$call) -> bool + 'static>>>);
			// NOTE: Safe only in wasm (guarded above) because there's only one thread.
			unsafe impl Send for ThisFilter {}
			unsafe impl Sync for ThisFilter {}

			static FILTER: ThisFilter = ThisFilter(RefCell::new(Vec::new()));

			impl Contains<$call> for $target {
				fn contains(call: &$call) -> bool {
					<$base>::contains(call) && FILTER.0.borrow().iter().all(|f| f(call))
				}
			}

			impl FilterStack<$call> for $target {
				type Stack = Vec<Box<dyn Fn(&$call) -> bool + 'static>>;
				fn push(f: impl Fn(&$call) -> bool + 'static) {
					FILTER.0.borrow_mut().push(Box::new(f));
				}
				fn pop() {
					FILTER.0.borrow_mut().pop();
				}
				fn take() -> Self::Stack {
					take(FILTER.0.borrow_mut().as_mut())
				}
				fn restore(mut s: Self::Stack) {
					swap(FILTER.0.borrow_mut().as_mut(), &mut s);
				}
			}
		}
	}
}

/// Type that provide some integrity tests.
///
/// This implemented for modules by `decl_module`.
#[impl_trait_for_tuples::impl_for_tuples(30)]
pub trait IntegrityTest {
	/// Run integrity test.
	///
	/// The test is not executed in a externalities provided environment.
	fn integrity_test() {}
}

#[cfg(test)]
pub mod test_impl_filter_stack {
	use super::*;

	pub struct IsCallable;
	pub struct BaseFilter;
	impl Contains<u32> for BaseFilter {
		fn contains(x: &u32) -> bool {
			x % 2 == 0
		}
	}
	impl_filter_stack!(
		crate::traits::filter::test_impl_filter_stack::IsCallable,
		crate::traits::filter::test_impl_filter_stack::BaseFilter,
		u32,
		is_callable
	);

	#[test]
	fn impl_filter_stack_should_work() {
		assert!(IsCallable::contains(&36));
		assert!(IsCallable::contains(&40));
		assert!(IsCallable::contains(&42));
		assert!(!IsCallable::contains(&43));

		IsCallable::push(|x| *x < 42);
		assert!(IsCallable::contains(&36));
		assert!(IsCallable::contains(&40));
		assert!(!IsCallable::contains(&42));

		IsCallable::push(|x| *x % 3 == 0);
		assert!(IsCallable::contains(&36));
		assert!(!IsCallable::contains(&40));

		IsCallable::pop();
		assert!(IsCallable::contains(&36));
		assert!(IsCallable::contains(&40));
		assert!(!IsCallable::contains(&42));

		let saved = IsCallable::take();
		assert!(IsCallable::contains(&36));
		assert!(IsCallable::contains(&40));
		assert!(IsCallable::contains(&42));
		assert!(!IsCallable::contains(&43));

		IsCallable::restore(saved);
		assert!(IsCallable::contains(&36));
		assert!(IsCallable::contains(&40));
		assert!(!IsCallable::contains(&42));

		IsCallable::pop();
		assert!(IsCallable::contains(&36));
		assert!(IsCallable::contains(&40));
		assert!(IsCallable::contains(&42));
		assert!(!IsCallable::contains(&43));
	}

	#[test]
	fn guards_should_work() {
		assert!(IsCallable::contains(&36));
		assert!(IsCallable::contains(&40));
		assert!(IsCallable::contains(&42));
		assert!(!IsCallable::contains(&43));
		{
			let _guard_1 = FilterStackGuard::<IsCallable, u32>::new(|x| *x < 42);
			assert!(IsCallable::contains(&36));
			assert!(IsCallable::contains(&40));
			assert!(!IsCallable::contains(&42));
			{
				let _guard_2 = FilterStackGuard::<IsCallable, u32>::new(|x| *x % 3 == 0);
				assert!(IsCallable::contains(&36));
				assert!(!IsCallable::contains(&40));
			}
			assert!(IsCallable::contains(&36));
			assert!(IsCallable::contains(&40));
			assert!(!IsCallable::contains(&42));
			{
				let _guard_2 = ClearFilterGuard::<IsCallable, u32>::new();
				assert!(IsCallable::contains(&36));
				assert!(IsCallable::contains(&40));
				assert!(IsCallable::contains(&42));
				assert!(!IsCallable::contains(&43));
			}
			assert!(IsCallable::contains(&36));
			assert!(IsCallable::contains(&40));
			assert!(!IsCallable::contains(&42));
		}
		assert!(IsCallable::contains(&36));
		assert!(IsCallable::contains(&40));
		assert!(IsCallable::contains(&42));
		assert!(!IsCallable::contains(&43));
	}
}
