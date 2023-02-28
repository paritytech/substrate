// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Provides functions to interact with the dispatch context.
//!
//! A Dispatch context is created by calling [`run_in_context`] and then the given closure will be
//! executed in this dispatch context. Everyting run in this `closure` will have access to the same
//! dispatch context. This also applies to nested calls of [`run_in_context`]. The dispatch context
//! can be used to store and retrieve information locally in this context. The dispatch context can
//! be accessed by using [`with_context`]. This function will execute the given closure and give it
//! access to the value stored in the dispatch context.
//!
//! # FRAME integration
//!
//! The FRAME macros implement [`UnfilteredDispatchable`](crate::traits::UnfilteredDispatchable) for
//! each pallet `Call` enum. Part of this implementation is the call to [`run_in_context`], so that
//! each call to
//! [`UnfilteredDispatchable::dispatch_bypass_filter`](crate::traits::UnfilteredDispatchable::dispatch_bypass_filter)
//! or [`Dispatchable::dispatch`](crate::dispatch::Dispatchable::dispatch) will run in a dispatch
//! context.
//!
//! # Example
//!
//! ```
//! use frame_support::dispatch_context::{with_context, run_in_context};
//!
//! // Not executed in a dispatch context, so it should return `None`.
//! assert!(with_context::<(), _>(|_| println!("Hello")).is_none());
//!
//! // Run it in a dispatch context and `with_context` returns `Some(_)`.
//! run_in_context(|| {
//!     assert!(with_context::<(), _>(|_| println!("Hello")).is_some());
//! });
//!
//! #[derive(Default)]
//! struct CustomContext(i32);
//!
//! run_in_context(|| {
//!     with_context::<CustomContext, _>(|v| {
//!         // Intitialize the value to the default value.
//!         assert_eq!(0, v.or_default().0);
//!         v.or_default().0 = 10;
//!     });
//!
//!     with_context::<CustomContext, _>(|v| {
//!         // We are still in the same context and can still access the set value.
//!         assert_eq!(10, v.or_default().0);
//!     });
//!
//!     run_in_context(|| {
//!         with_context::<CustomContext, _>(|v| {
//!             // A nested call of `run_in_context` stays in the same dispatch context
//!             assert_eq!(10, v.or_default().0);
//!         })
//!     })
//! });
//!
//! run_in_context(|| {
//!     with_context::<CustomContext, _>(|v| {
//!         // We left the other context and created a new one, so we should be back
//!         // to our default value.
//!         assert_eq!(0, v.or_default().0);
//!     });
//! });
//! ```
//!
//! In your pallet you will only have to use [`with_context`], because as described above
//! [`run_in_context`] will be handled by FRAME for you.

use sp_std::{
	any::{Any, TypeId},
	boxed::Box,
	collections::btree_map::{BTreeMap, Entry},
};

environmental::environmental!(DISPATCH_CONTEXT: BTreeMap<TypeId, Box<dyn Any>>);

/// Abstraction over some optional value `T` that is stored in the dispatch context.
pub struct Value<'a, T> {
	value: Option<&'a mut T>,
	new_value: Option<T>,
}

impl<T> Value<'_, T> {
	/// Get the value as reference.
	pub fn get(&self) -> Option<&T> {
		self.new_value.as_ref().or_else(|| self.value.as_ref().map(|v| *v as &T))
	}

	/// Get the value as mutable reference.
	pub fn get_mut(&mut self) -> Option<&mut T> {
		self.new_value.as_mut().or_else(|| self.value.as_mut().map(|v| *v as &mut T))
	}

	/// Set to the given value.
	///
	/// [`Self::get`] and [`Self::get_mut`] will return `new_value` afterwards.
	pub fn set(&mut self, new_value: T) {
		self.value = None;
		self.new_value = Some(new_value);
	}

	/// Returns a mutable reference to the value.
	///
	/// If the internal value isn't initialized, this will set it to [`Default::default()`] before
	/// returning the mutable reference.
	pub fn or_default(&mut self) -> &mut T
	where
		T: Default,
	{
		if let Some(v) = &mut self.value {
			return v
		}

		self.new_value.get_or_insert_with(|| Default::default())
	}

	/// Clear the internal value.
	///
	/// [`Self::get`] and [`Self::get_mut`] will return `None` afterwards.
	pub fn clear(&mut self) {
		self.new_value = None;
		self.value = None;
	}
}

/// Runs the given `callback` in the dispatch context and gives access to some user defined value.
///
/// Passes the a mutable reference of [`Value`] to the callback. The value will be of type `T` and
/// is identified using the [`TypeId`] of `T`. This means that `T` should be some unique type to
/// make the value unique. If no value is set yet [`Value::get()`] and [`Value::get_mut()`] will
/// return `None`. It is totally valid to have some `T` that is shared between different callers to
/// have access to the same value.
///
/// Returns `None` if the current context is not a dispatch context. To create a context it is
/// required to call [`run_in_context`] with the closure to execute in this context. So, for example
/// in tests it could be that there isn't any dispatch context or when calling a dispatchable like a
/// normal Rust function from some FRAME hook.
pub fn with_context<T: 'static, R>(callback: impl FnOnce(&mut Value<T>) -> R) -> Option<R> {
	DISPATCH_CONTEXT::with(|c| match c.entry(TypeId::of::<T>()) {
		Entry::Occupied(mut o) => {
			let value = o.get_mut().downcast_mut::<T>();

			if value.is_none() {
				log::error!(
					"Failed to downcast value for type {} in dispatch context!",
					sp_std::any::type_name::<T>(),
				);
			}

			let mut value = Value { value, new_value: None };
			let res = callback(&mut value);

			if value.value.is_none() && value.new_value.is_none() {
				o.remove();
			} else if let Some(new_value) = value.new_value {
				o.insert(Box::new(new_value) as Box<_>);
			}

			res
		},
		Entry::Vacant(v) => {
			let mut value = Value { value: None, new_value: None };

			let res = callback(&mut value);

			if let Some(new_value) = value.new_value {
				v.insert(Box::new(new_value) as Box<_>);
			}

			res
		},
	})
}

/// Run the given closure `run` in a dispatch context.
///
/// Nested calls to this function will execute `run` in the same dispatch context as the initial
/// call to this function. In other words, all nested calls of this function will be done in the
/// same dispatch context.
pub fn run_in_context<R>(run: impl FnOnce() -> R) -> R {
	DISPATCH_CONTEXT::using_once(&mut Default::default(), run)
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn dispatch_context_works() {
		// No context, so we don't execute
		assert!(with_context::<(), _>(|_| ()).is_none());

		let ret = run_in_context(|| with_context::<(), _>(|_| 1).unwrap());
		assert_eq!(1, ret);

		#[derive(Default)]
		struct Context(i32);

		let res = run_in_context(|| {
			with_context::<Context, _>(|v| {
				assert_eq!(0, v.or_default().0);

				v.or_default().0 = 100;
			});

			run_in_context(|| {
				run_in_context(|| {
					run_in_context(|| with_context::<Context, _>(|v| v.or_default().0).unwrap())
				})
			})
		});

		// Ensure that the initial value set in the context is also accessible after nesting the
		// `run_in_context` calls.
		assert_eq!(100, res);
	}
}
