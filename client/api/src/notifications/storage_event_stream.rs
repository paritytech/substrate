// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use futures::Stream;
use std::{pin::Pin, task::Poll};

use sc_utils::{mpsc::TracingUnboundedReceiver, pubsub::SubscriptionGuard};

/// Type that implements `futures::Stream` of storage change events.
pub struct StorageEventStream<H> {
	// NB: this field should be declared before the `rx`.
	// (The fields of a struct are dropped in declaration order.)[https://doc.rust-lang.org/reference/destructors.html]
	pub(super) _subs_guard: SubscriptionGuard<StorageNotificationsImpl<H>>,

	// NB: this field should be declared after the `_subs_guard`.
	pub(super) rx: TracingUnboundedReceiver<Notification<H>>,
	pub(super) was_triggered: bool,
}

impl<H> Stream for StorageEventStream<H> {
	type Item = <TracingUnboundedReceiver<Notification<H>> as Stream>::Item;
	fn poll_next(
		mut self: Pin<&mut Self>,
		cx: &mut std::task::Context<'_>,
	) -> Poll<Option<Self::Item>> {
		let result = Stream::poll_next(Pin::new(&mut self.rx), cx);
		if result.is_ready() {
			self.was_triggered = true;
		}
		result
	}
}
