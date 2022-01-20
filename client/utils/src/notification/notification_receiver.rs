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

use std::{
	pin::Pin,
	task::{Context, Poll},
};

use ::futures::stream::{FusedStream, Stream};

/// The receiving half of the notifications channel(s).
#[derive(Debug)]
pub struct NotificationReceiver<Payload> {
	pub(super) subs_guard: SubscriptionGuard<Registry<Payload>, TracingUnboundedReceiver<Payload>>,
}

impl<Payload> Unpin for NotificationReceiver<Payload> {}

impl<Payload> Stream for NotificationReceiver<Payload> {
	type Item = Payload;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Payload>> {
		Pin::new(self.get_mut().subs_guard.rx_mut()).poll_next(cx)
	}
}

impl<Payload> FusedStream for NotificationReceiver<Payload> {
	fn is_terminated(&self) -> bool {
		self.subs_guard.rx().is_terminated()
	}
}
