// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use parking_lot::Mutex;
use std::sync::Arc;

use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_runtime::traits::Block as BlockT;

use crate::{justification::GrandpaJustification, Error};

// Stream of justifications returned when subscribing.
type JustificationStream<Block> = TracingUnboundedReceiver<GrandpaJustification<Block>>;

// Sending endpoint for notifying about justifications.
type JustificationSender<Block> = TracingUnboundedSender<GrandpaJustification<Block>>;

// Collection of channel sending endpoints shared with the receiver side so they can register
// themselves.
type SharedJustificationSenders<Block> = Arc<Mutex<Vec<JustificationSender<Block>>>>;

/// The sending half of the Grandpa justification channel(s).
///
/// Used to send notifications about justifications generated
/// at the end of a Grandpa round.
#[derive(Clone)]
pub struct GrandpaJustificationSender<Block: BlockT> {
	subscribers: SharedJustificationSenders<Block>,
}

impl<Block: BlockT> GrandpaJustificationSender<Block> {
	/// The `subscribers` should be shared with a corresponding
	/// `GrandpaJustificationStream`.
	fn new(subscribers: SharedJustificationSenders<Block>) -> Self {
		Self { subscribers }
	}

	/// Send out a notification to all subscribers that a new justification
	/// is available for a block.
	pub fn notify(
		&self,
		justification: impl FnOnce() -> Result<GrandpaJustification<Block>, Error>,
	) -> Result<(), Error> {
		let mut subscribers = self.subscribers.lock();

		// do an initial prune on closed subscriptions
		subscribers.retain(|n| !n.is_closed());

		// if there's no subscribers we avoid creating
		// the justification which is a costly operation
		if !subscribers.is_empty() {
			let justification = justification()?;
			subscribers.retain(|n| n.unbounded_send(justification.clone()).is_ok());
		}

		Ok(())
	}
}

/// The receiving half of the Grandpa justification channel.
///
/// Used to receive notifications about justifications generated
/// at the end of a Grandpa round.
/// The `GrandpaJustificationStream` entity stores the `SharedJustificationSenders`
/// so it can be used to add more subscriptions.
#[derive(Clone)]
pub struct GrandpaJustificationStream<Block: BlockT> {
	subscribers: SharedJustificationSenders<Block>,
}

impl<Block: BlockT> GrandpaJustificationStream<Block> {
	/// Creates a new pair of receiver and sender of justification notifications.
	pub fn channel() -> (GrandpaJustificationSender<Block>, Self) {
		let subscribers = Arc::new(Mutex::new(vec![]));
		let receiver = GrandpaJustificationStream::new(subscribers.clone());
		let sender = GrandpaJustificationSender::new(subscribers.clone());
		(sender, receiver)
	}

	/// Create a new receiver of justification notifications.
	///
	/// The `subscribers` should be shared with a corresponding
	/// `GrandpaJustificationSender`.
	fn new(subscribers: SharedJustificationSenders<Block>) -> Self {
		Self { subscribers }
	}

	/// Subscribe to a channel through which justifications are sent
	/// at the end of each Grandpa voting round.
	pub fn subscribe(&self) -> JustificationStream<Block> {
		let (sender, receiver) = tracing_unbounded("mpsc_justification_notification_stream");
		self.subscribers.lock().push(sender);
		receiver
	}
}
