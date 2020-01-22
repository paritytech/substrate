// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! rpc api for babe.

use crate::BabeClaim;
use futures_channel as state;
use futures::{prelude::*, future};
use jsonrpc_core::{BoxFuture, Error, ErrorCode};
use jsonrpc_derive::rpc;
use sc_consensus_slots::SlotWorkerEvent;
use std::sync::Arc;

/// Provides rpc methods for interacting with Babe
#[rpc]
pub trait Babe {
	/// query slot authorship info
//	#[rpc(name = "babe_slotAuthorship")]
	fn slot_authorship(&self) -> BoxFuture<Arc<SlotWorkerEvent<BabeClaim>>>;
}

/// RPC handler for Babe
/// provides `babe_slotAuthorship` method for querying slot authorship data.
struct BabeRPC {
	receiver: state::Receiver<SlotWorkerEvent<BabeClaim>>,
}

impl Babe for BabeRPC {
	fn slot_authorship(&self) -> BoxFuture<Arc<SlotWorkerEvent<BabeClaim>>> {
		let stream = self.receiver.clone();
		let mut stream = stream
			.filter(|e| {
				future::ready(match **e {
					SlotWorkerEvent::NewSlot { .. } => false,
					_ => true
				})
			});

		let future = async move {
			if let Some(event) = stream.next().await {
				Ok(event)
			} else {
				Err(Error {
					code: ErrorCode::ServerError(1234),
					message: "lol".into(),
					data: None
				})
			}
		}.boxed();

		Box::new(future.compat())
	}
}
