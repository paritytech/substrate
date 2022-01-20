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

/// The sending half of the notifications channel(s).
///
/// Used to send notifications from the BEEFY gadget side.
pub struct NotificationSender<Payload> {
	registry: SharedRegistry<Registry<Payload>>,
}

impl<Payload> Clone for NotificationSender<Payload> {
	fn clone(&self) -> Self {
		Self { registry: self.registry.clone() }
	}
}

impl<Payload> NotificationSender<Payload> {
	/// Send out a notification to all subscribers that a new payload is available for a
	/// block.
	pub fn notify<Error>(
		&self,
		payload: impl FnOnce() -> Result<Payload, Error>,
	) -> Result<(), Error>
	where
		Payload: Clone,
	{
		// The subscribers collection used to be cleaned upon send previously.
		// The set used to be cleaned up twice:
		// - once before sending: filter on `!tx.is_closed()`;
		// - once while sending: filter on `!tx.unbounded_send().is_err()`.
		//
		// Since there is no `close` or `disconnect` operation defined on the
		// `NotificationReceiver<Payload>`, the only way to close the `rx` is to drop it.
		// Upon being dropped the `NotificationReceiver<Payload>` unregisters its `rx`
		// from the registry using its `_subs_guard`.
		//
		// So there's no need to clean up the subscribers set upon sending another message.

		let registry = self.registry.lock();
		let subscribers = &registry.subscribers;

		if !subscribers.is_empty() {
			let payload = payload()?;
			for (_subs_id, tx) in subscribers {
				let _ = tx.unbounded_send(payload.clone());
			}
		}

		Ok(())
	}

	/// The `subscribers` should be shared with a corresponding `NotificationStream`.
	pub(super) fn new(registry: SharedRegistry<Registry<Payload>>) -> Self {
		Self { registry }
	}
}
