// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! Provides means to implement a typical Pub/Sub mechanism.
//!
//! When implementing a Pub/Sub it is usual to introduce types for
//! the *producer*-side and the *consumer*-side.
//! The *producer* keeps track on its *consumers* using a *registry*.
//! That *registry* needs to be shared between both the *producer* and its *consumers*:
//! - the *producer* — to dispatch the broadcast messages;
//! - the *consumer* — in order to subscribe and unsubscribe.
//!
//! According to this module's idea,
//! the shared *registry* should implement the following traits: `SubsBase`,
//! `Subscribe<SubscribeOp>`, `Unsubscribe`.
//!
//! The *registry* upon subscription yields a subscription ID (defined as `SubsBase::SubsID`).
//! The implementation should not usually touch the subscription ID from outside of the *registry*.
//!
//! The *producer* then holds a reference to the shared *registry* by wrapping it into
//! `SharedRegistry<R>` (where `R` is the *registry*).
//!
//! The consumers hold a weak reference to the *registry* by having it wrapped
//! into a `SubscriptionGuard<R>` (where `R` is the *registry*), along with the *consumer's*
//! subsription ID. The unsubscription is done by the `SubscriptionGuard<R>` upon drop.

use std::{
	ops::DerefMut,
	sync::{Arc, Weak},
};

use ::parking_lot::Mutex;

pub trait SubsBase {
	type SubsID;
}

pub trait Subscribe<Op>: SubsBase {
	fn subscribe(&mut self, subs_op: Op) -> Self::SubsID;
}

pub trait Unsubscribe: SubsBase {
	fn unsubscribe(&mut self, subs_id: &Self::SubsID);
}

/// A wrapper to share the internal subscription registry.
///
/// Provides convenience methods to access the underlying registry.
#[derive(Debug)]
pub struct SharedRegistry<R> {
	registry: Arc<Mutex<R>>,
}

/// A guard structure wrapping `R: Unsubscribe`, that will perform unsubscription upon being
/// dropped.
pub struct SubscriptionGuard<R, Rx>
where
	R: Unsubscribe,
{
	// NB: this field must be declared before the `rx`.
	// (The fields of a struct are dropped in declaration order.)[https://doc.rust-lang.org/reference/destructors.html]
	inner: SubscriptionGuardInner<R>,

	// NB: this field must be declared after the `inner`.
	rx: Rx,
}

struct SubscriptionGuardInner<R>
where
	R: Unsubscribe,
{
	registry: Weak<Mutex<R>>,
	subs_id: R::SubsID,
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
	pub fn subscribe<Op>(&self, subs_op: Op) -> SubscriptionGuard<R, ()>
	where
		R: Subscribe<Op> + Unsubscribe,
	{
		let subs_id = self.lock().subscribe(subs_op);
		let inner = SubscriptionGuardInner { registry: Arc::downgrade(&self.registry), subs_id };
		SubscriptionGuard { inner, rx: () }
	}
}

impl<R> SubscriptionGuard<R, ()>
where
	R: Unsubscribe,
{
	/// This method is only defined for the case when the current `Rx` is `()`,
	/// so that no `Rx` other than `()` shall not be dropped before the unsubscription is performed.
	pub fn with_rx<Rx>(self, rx: Rx) -> SubscriptionGuard<R, Rx> {
		SubscriptionGuard { inner: self.inner, rx }
	}
}

impl<R, Rx> SubscriptionGuard<R, Rx>
where
	R: Unsubscribe,
{
	pub fn rx(&self) -> &Rx {
		&self.rx
	}
	pub fn rx_mut(&mut self) -> &mut Rx {
		&mut self.rx
	}
}

impl<R> Drop for SubscriptionGuardInner<R>
where
	R: Unsubscribe,
{
	fn drop(&mut self) {
		if let Some(registry) = self.registry.upgrade() {
			let () = registry.lock().unsubscribe(&self.subs_id);
		}
	}
}

impl<R, Rx> std::fmt::Debug for SubscriptionGuard<R, Rx>
where
	R: Unsubscribe + std::fmt::Debug,
	R::SubsID: std::fmt::Debug,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_struct("SubscriptionGuard")
			.field("registry", &self.inner.registry)
			.field("subs_id", &self.inner.subs_id)
			.finish()
	}
}
