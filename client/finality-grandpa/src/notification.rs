// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use std::sync::Arc;
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};

use sp_runtime::traits::Block as BlockT;
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedSender, TracingUnboundedReceiver};

/// Justification for a finalized block.
#[derive(Clone, Serialize, Deserialize)]
pub struct JustificationNotification<Block: BlockT> {
	/// Highest finalized block header
	pub header: Block::Header,
	/// An encoded justification proving that the given header has been finalized
	pub justification: Vec<u8>,
}

// Stream of justifications returned when subscribing.
type JustificationStream<Block> = TracingUnboundedReceiver<JustificationNotification<Block>>;

// Sending endpoint for notifying about justifications.
type FinalityNotifier<T> = TracingUnboundedSender<JustificationNotification<T>>;

// Collection of channel sending endpoints shared with the receiver side so they can register
// themselves.
type SharedFinalityNotifiers<T> = Arc<Mutex<Vec<FinalityNotifier<T>>>>;

/// The sending half of the Grandpa justification channel.
///
/// Used to send notifictions about justifications generated
/// at the end of a Grandpa round.
#[derive(Clone)]
pub struct GrandpaJustificationSender<Block: BlockT> {
	notifiers: SharedFinalityNotifiers<Block>
}

impl<Block: BlockT> GrandpaJustificationSender<Block> {
	/// The `notifiers` should be shared with a corresponding
	/// `GrandpaJustificationReceiver`.
	fn new(notifiers: SharedFinalityNotifiers<Block>) -> Self {
		Self {
			notifiers,
		}
	}

	/// Send out a notification to all subscribers that a new justification
	/// is available for a block.
	pub fn notify(&self, notification: JustificationNotification<Block>) -> Result<(), ()> {
		self.notifiers.lock()
			.retain(|n| {
				!n.is_closed() || n.unbounded_send(notification.clone()).is_ok()
			});

		Ok(())
	}
}

/// The receiving half of the Grandpa justification channel.
///
/// Used to recieve notifictions about justifications generated
/// at the end of a Grandpa round.
#[derive(Clone)]
pub struct GrandpaJustificationReceiver<Block: BlockT> {
	notifiers: SharedFinalityNotifiers<Block>
}

impl<Block: BlockT> GrandpaJustificationReceiver<Block> {
	/// Creates a new pair of receiver and sender of justification notifications.
	pub fn channel() -> (GrandpaJustificationSender<Block>, Self) {
		let finality_notifiers = Arc::new(Mutex::new(vec![]));
		let receiver = GrandpaJustificationReceiver::new(finality_notifiers.clone());
		let sender = GrandpaJustificationSender::new(finality_notifiers.clone());
		(sender, receiver)
	}

	/// Create a new receiver of justification notifications.
	///
	/// The `notifiers` should be shared with a corresponding
	/// `GrandpaJustificationSender`.
	fn new(notifiers: SharedFinalityNotifiers<Block>) -> Self {
		Self {
			notifiers,
		}
	}

	/// Subscribe to a channel through which justifications are sent
	/// at the end of each Grandpa voting round.
	pub fn subscribe(&self) -> JustificationStream<Block> {
		let (sender, receiver) = tracing_unbounded("mpsc_justification_notification_stream");
		self.notifiers.lock().push(sender);
		receiver
	}
}
