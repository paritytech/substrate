// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use std::collections::HashSet;

use crate::{
	id_sequence::SeqID,
	pubsub::{Dispatch, Subscribe, Unsubscribe},
};

/// The shared structure to keep track on subscribers.
#[derive(Debug, Default)]
pub(super) struct Registry {
	pub(super) subscribers: HashSet<SeqID>,
}

impl Subscribe<()> for Registry {
	fn subscribe(&mut self, _subs_key: (), subs_id: SeqID) {
		self.subscribers.insert(subs_id);
	}
}
impl Unsubscribe for Registry {
	fn unsubscribe(&mut self, subs_id: SeqID) {
		self.subscribers.remove(&subs_id);
	}
}

impl<MakePayload, Payload, Error> Dispatch<MakePayload> for Registry
where
	MakePayload: FnOnce() -> Result<Payload, Error>,
	Payload: Clone,
{
	type Item = Payload;
	type Ret = Result<(), Error>;

	fn dispatch<F>(&mut self, make_payload: MakePayload, mut dispatch: F) -> Self::Ret
	where
		F: FnMut(&SeqID, Self::Item),
	{
		if !self.subscribers.is_empty() {
			let payload = make_payload()?;
			for subs_id in &self.subscribers {
				dispatch(subs_id, payload.clone());
			}
		}
		Ok(())
	}
}
