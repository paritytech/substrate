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

mod subscription;
pub use subscription::{SubsBase, Subscribe, Unsubscribe};

mod shared_registry;
pub use shared_registry::{SharedRegistry, SubscriptionGuard};
