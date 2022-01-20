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

use super::*;

/// The receiving half of the notifications channel.
///
/// The `NotificationStream` entity stores the `SharedSenders` so it can be
/// used to add more subscriptions.
#[derive(Clone)]
pub struct NotificationStream<Payload, TK: TracingKeyStr> {
	registry: SharedRegistry<Registry<Payload>>,
	_pd: std::marker::PhantomData<TK>,
}

impl<Payload, TK: TracingKeyStr> NotificationStream<Payload, TK> {
	/// Creates a new pair of receiver and sender of `Payload` notifications.
	pub fn channel() -> (NotificationSender<Payload>, Self) {
		let registry = SharedRegistry::<Registry<Payload>>::default();
		let sender = NotificationSender::new(registry.clone());
		let receiver = NotificationStream::new(registry);
		(sender, receiver)
	}

	/// Create a new receiver of `Payload` notifications.
	///
	/// The `subscribers` should be shared with a corresponding `NotificationSender`.
	fn new(registry: SharedRegistry<Registry<Payload>>) -> Self {
		Self { registry, _pd: Default::default() }
	}

	/// Subscribe to a channel through which the generic payload can be received.
	pub fn subscribe(&self) -> NotificationReceiver<Payload> {
		let (underlying_tx, underlying_rx) = crate::mpsc::tracing_unbounded(TK::TRACING_KEY);
		let subs_guard = self.registry.subscribe(underlying_tx).with_rx(underlying_rx);
		let receiver = NotificationReceiver { subs_guard };
		receiver
	}
}
