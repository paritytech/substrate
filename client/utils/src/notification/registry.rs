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

use crate::pubsub::{SubsBase, Subscribe, Unsubscribe};

/// The shared structure to keep track on subscribers.
#[derive(Debug)]
pub(super) struct Registry<Payload> {
	pub(super) id_sequence: IDSequence,
	pub(super) subscribers: HashMap<SeqID, TracingUnboundedSender<Payload>>,
}

impl<Payload> Default for Registry<Payload> {
	fn default() -> Self {
		Self { id_sequence: Default::default(), subscribers: Default::default() }
	}
}

impl<Payload> SubsBase for Registry<Payload> {
	type SubsID = SeqID;
}
impl<Payload> Unsubscribe for Registry<Payload> {
	fn unsubscribe(&mut self, subs_id: &Self::SubsID) {
		let _ = self.subscribers.remove(subs_id);
	}
}

impl<Payload> Subscribe<TracingUnboundedSender<Payload>> for Registry<Payload> {
	fn subscribe(&mut self, subs_op: TracingUnboundedSender<Payload>) -> Self::SubsID {
		let subs_id = self.id_sequence.next_id();
		assert!(self.subscribers.insert(subs_id, subs_op).is_none(), "
			Each `subs_id` is taken from `self.id_sequence.next_id()`.
			If we have a duplicate key here, it's either the implementation of `IDSequence` was broken, or we've overflowed `u64`.
			We are not likely to overflow an `u64`.");
		subs_id
	}
}
