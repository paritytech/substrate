// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use crate::schema::v1::{StateRequest, StateResponse};
use crate::chain::Client;
use crate::protocol::message;
use super::state::StateSync;
use crate::StateDownloadProgress;
pub use super::state::ImportResult;

/// Warp sync support.

enum Phase<B: BlockT> {
	Block,
	State(StateSync<B>),
}

/// Warp sync state machine. Accumulates target header, warp proofs, state.
pub struct WarpSync<B: BlockT> {
	target_hash: B::Hash,
	target_num: NumberFor<B>,
	phase: Phase<B>,
	client: Arc<dyn Client<B>>,
}

impl<B: BlockT> WarpSync<B> {
	///  Create a new instance.
	pub fn new(client: Arc<dyn Client<B>>, target_hash: B::Hash, target_num: NumberFor<B>) -> Self {
		WarpSync {
			client,
			target_hash,
			target_num,
			phase: Phase::Block,
		}
	}

	///  Validate and import a state reponse.
	pub fn import_state(&mut self, response: StateResponse) -> ImportResult<B> {
		match &mut self.phase {
			Phase::Block => {
				log::debug!(
					target: "sync",
					"Unexpected state response",
				);
				return ImportResult::BadResponse;
			}
			Phase::State(sync) => sync.import(response)
		}
	}

	///  Validate and import a block reponse.
	pub fn import_block(&mut self, mut response: message::BlockResponse<B>) -> ImportResult<B> {
		match &mut self.phase {
			Phase::Block => {
				if response.blocks.len() != 1 {
					log::debug!( target: "sync", "Bad block response");
					return ImportResult::BadResponse;
				}
				let header = match response.blocks.pop().and_then(|r| r.header) {
					Some(header) => header,
					None => {
						log::debug!( target: "sync", "No header in the response");
						return ImportResult::BadResponse;
					}
				};
				if header.hash() != self.target_hash {
					log::debug!( target: "sync", "Bad header in the response");
					return ImportResult::BadResponse;
				}
				let state_sync = StateSync::new(self.client.clone(), header, false);
				let request = state_sync.next_request();
				self.phase = Phase::State(state_sync);
				log::debug!( target: "sync", "Warp header received.");
				ImportResult::Continue(request)
			}
			Phase::State(_) => {
				log::debug!(
					target: "sync",
					"Unexpected block response",
				);
				ImportResult::BadResponse
			}
		}
	}

	/// Produce next state request.
	pub fn next_block_request(&self) -> Option<message::BlockRequest<B>> {
		match &self.phase {
			Phase::Block => Some(message::generic::BlockRequest {
				id: 0,
				fields: message::BlockAttributes::HEADER,
				from: message::FromBlock::Hash(self.target_hash),
				to: None,
				direction: message::Direction::Ascending,
				max: Some(1)
			}),
			Phase::State(_) => None,
		}
	}

	/// Produce next state request.
	pub fn next_state_request(&self) -> Option<StateRequest> {
		match &self.phase {
			Phase::Block => None,
			Phase::State(sync) => Some(sync.next_request())
		}
	}

	/// Return target block number.
	pub fn target_block_number(&self) -> NumberFor<B> {
		self.target_num
	}

	/// Check if the state is complete.
	pub fn is_complete(&self) -> bool {
		match &self.phase {
			Phase::Block => false,
			Phase::State(sync) => sync.is_complete(),
		}
	}

	/// Returns state sync estimated progress (percentage, bytes)
	pub fn progress(&self) -> StateDownloadProgress {
		match &self.phase {
			Phase::Block => StateDownloadProgress {
				percentage: 0,
				size: 0,
			},
			Phase::State(sync) => sync.progress(),
		}
	}
}

