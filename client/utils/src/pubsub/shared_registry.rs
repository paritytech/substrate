// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use super::*;

use std::{
	ops::DerefMut,
	sync::{Arc, Weak},
};

use ::parking_lot::Mutex;

/// A wrapper to share the internal subscription registry.
///
/// Provides convenience methods to access the underlying registry.
#[derive(Debug)]
pub struct SharedRegistry<R> {
	registry: Arc<Mutex<R>>,
}
impl<R> Clone for SharedRegistry<R> {
	fn clone(&self) -> Self {
		Self { registry: self.registry.clone() }
	}
}
impl<R> Default for SharedRegistry<R>
where
	R: Default,
{
	fn default() -> Self {
		Self::new(Default::default())
	}
}

/// A guard structure that will perform unsubscription upon being dropped.
#[derive(Debug)]
pub struct SubscriptionGuard<R>
where
	R: Unsubscribe,
{
	registry: Weak<Mutex<R>>,
	subs_id: R::SubsID,
}

impl<R> SharedRegistry<R> {
	pub fn new(registry: R) -> Self {
		let registry = Arc::new(Mutex::new(registry));
		Self { registry }
	}

	/// Lock the underlying registry and provide an access to it via a MutexGuard.
	pub fn lock<'a>(&'a self) -> impl DerefMut<Target = R> + 'a {
		self.registry.lock()
	}

	/// Subscribe to the registry and return a `SubscriptionGuard<R>`.
	///
	/// This method invokes the underlying registry's `Subscribe<Op>::subscribe(Op)` method
	/// but instead of returning a `SubsBase::SubsID`, wraps it into a `SubscriptionGuard<R>`.
	/// Since the `SubscriptionGuard<R>` is not cloneable it is always moved,
	/// thus it is always clear when the unsubscription shall be performed.
	pub fn subscribe<Op>(&self, subs_op: Op) -> SubscriptionGuard<R>
	where
		R: Subscribe<Op> + Unsubscribe,
	{
		let subs_id = self.lock().subscribe(subs_op);
		SubscriptionGuard { registry: Arc::downgrade(&self.registry), subs_id }
	}
}

impl<R> Drop for SubscriptionGuard<R>
where
	R: Unsubscribe,
{
	fn drop(&mut self) {
		if let Some(registry) = self.registry.upgrade() {
			let () = registry.lock().unsubscribe(&self.subs_id);
		}
	}
}
