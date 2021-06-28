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
use sp_runtime::traits::{Block as BlockT, Header, NumberFor, Zero};
use sp_finality_grandpa::{SetId, AuthorityList};
use crate::schema::v1::{StateRequest, StateResponse};
use crate::chain::Client;
use crate::protocol::message;
use super::state::StateSync;
use crate::StateDownloadProgress;
pub use crate::warp_request_handler::{
	Request as WarpProofRequest, WarpSyncProvider, EncodedProof, VerificationResult,
	EncodedJustification,
};
pub use super::state::ImportResult;

/// Warp sync support.

enum Phase<B: BlockT> {
	Block,
	WarpProof {
		set_id: SetId,
		authorities: AuthorityList,
		target_justification: EncodedJustification,
		target_header: B::Header,
		last_hash: B::Hash,
	},
	State(StateSync<B>),
}

/// Import warp proof result.
pub enum WarpProofImportResult<B: BlockT> {
	/// Start downloading state data.
	StateRequest(StateRequest),
	/// Continue dowloading warp sync proofs.
	WarpProofRequest(WarpProofRequest<B>),
	/// Bad proof.
	BadResponse,
}

pub enum WarpBlockImportResult<B: BlockT> {
	/// Start downloading state data.
	WarpProofRequest(WarpProofRequest<B>),
	/// Bad block data.
	BadResponse,
}

/// Warp sync state machine. Accumulates target header, warp proofs, state.
pub struct WarpSync<B: BlockT> {
	target_hash: B::Hash,
	target_num: NumberFor<B>,
	phase: Phase<B>,
	client: Arc<dyn Client<B>>,
	warp_sync_provider: Arc<dyn WarpSyncProvider<B>>,
}

impl<B: BlockT> WarpSync<B> {
	///  Create a new instance.
	pub fn new(
		client: Arc<dyn Client<B>>,
		warp_sync_provider: Arc<dyn WarpSyncProvider<B>>,
		target_num: NumberFor<B>
	) -> Self {
		WarpSync {
			client,
			warp_sync_provider,
			target_hash: Default::default(),
			target_num,
			phase: Phase::Block,
		}
	}

	///  Validate and import a state reponse.
	pub fn import_state(&mut self, response: StateResponse) -> ImportResult<B> {
		match &mut self.phase {
			Phase::Block | Phase::WarpProof {..} => {
				log::debug!(target: "sync", "Unexpected state response");
				return ImportResult::BadResponse;
			}
			Phase::State(sync) => sync.import(response)
		}
	}

	///  Validate and import a warp proof reponse.
	pub fn import_warp_proof(&mut self, response: EncodedProof) -> WarpProofImportResult<B> {
		match &mut self.phase {
			Phase::Block | Phase::State(_) => {
				log::debug!(target: "sync", "Unexpected warp proof response");
				WarpProofImportResult::BadResponse
			},
			Phase::WarpProof { set_id, authorities, target_justification, target_header, last_hash } => {
				match self.warp_sync_provider.verify(
					&response,
					*set_id,
					std::mem::take(authorities),
					target_header,
					target_justification,
				) {
					Err(e) => {
						log::debug!( target: "sync", "Bad warp proof response: {:?}", e);
						return WarpProofImportResult::BadResponse;
					},
					Ok(VerificationResult::Partial(new_set_id, new_authorities, new_last_hash)) => {
						*set_id = new_set_id;
						*authorities = new_authorities;
						*last_hash = new_last_hash.clone();
						WarpProofImportResult::WarpProofRequest(WarpProofRequest {
							begin: new_last_hash
						})
					},
					Ok(VerificationResult::Complete(_, _)) =>  {
						let state_sync = StateSync::new(self.client.clone(), target_header.clone(), false);
						let request = state_sync.next_request();
						self.phase = Phase::State(state_sync);
						WarpProofImportResult::StateRequest(request)
					}
				}
			}
		}
	}

	///  Validate and import a block reponse.
	pub fn import_block(&mut self, mut response: message::BlockResponse<B>) -> WarpBlockImportResult<B> {
		match &mut self.phase {
			Phase::Block => {
				if response.blocks.len() != 1 {
					log::debug!( target: "sync", "Bad block response");
					return WarpBlockImportResult::BadResponse;
				}
				let (header, justification) = match response.blocks.pop()
					.map(|r| (r.header, r.justification))
				{
					Some((Some(header), Some(justification))) => (header, justification),
					_ => {
						log::debug!( target: "sync", "No header or justification in the response");
						return WarpBlockImportResult::BadResponse;
					}
				};
				self.target_hash = header.hash();
				log::debug!( target: "sync", "Warp header received.");

				//TODO: error here
				let last_hash = self.client.hash(Zero::zero()).unwrap()
					.expect("Genesis header always exists");
				self.phase = Phase::WarpProof {
					set_id: 0,
					authorities: AuthorityList::default(),
					target_justification: EncodedJustification(justification),
					target_header: header,
					last_hash: last_hash.clone(),
				};

				let request = WarpProofRequest { begin: last_hash };
				WarpBlockImportResult::WarpProofRequest(request)
			}
			Phase::State(_) | Phase::WarpProof {..} => {
				log::debug!(
					target: "sync",
					"Unexpected block response",
				);
				WarpBlockImportResult::BadResponse
			}
		}
	}

	/// Produce next state request.
	pub fn next_block_request(&self) -> Option<message::BlockRequest<B>> {
		match &self.phase {
			Phase::Block => Some(message::generic::BlockRequest {
				id: 0,
				fields: message::BlockAttributes::HEADER,
				from: message::FromBlock::Number(self.target_num),
				to: None,
				direction: message::Direction::Ascending,
				max: Some(1)
			}),
			Phase::State(_) | Phase::WarpProof {..}  => None,
		}
	}

	/// Produce next state request.
	pub fn next_state_request(&self) -> Option<StateRequest> {
		match &self.phase {
			Phase::Block | Phase::WarpProof {..} => None,
			Phase::State(sync) => Some(sync.next_request())
		}
	}

	/// Produce next warp proof request.
	pub fn next_warp_poof_request(&self) -> Option<WarpProofRequest<B>> {
		match &self.phase {
			Phase::Block | Phase::State(_) => None,
			Phase::WarpProof { last_hash, .. } => {
				Some(WarpProofRequest {
					begin: last_hash.clone(),
				})
			}
		}
	}

	/// Return target block hash.
	pub fn target_block_hash(&self) -> B::Hash {
		self.target_hash.clone()
	}

	/// Return target block number.
	pub fn target_block_number(&self) -> NumberFor<B> {
		self.target_num
	}

	/// Check if the state is complete.
	pub fn is_complete(&self) -> bool {
		match &self.phase {
			Phase::Block | Phase::WarpProof {..} => false,
			Phase::State(sync) => sync.is_complete(),
		}
	}

	/// Returns state sync estimated progress (percentage, bytes)
	pub fn progress(&self) -> StateDownloadProgress {
		match &self.phase {
			Phase::Block | Phase::WarpProof {..} => StateDownloadProgress {
				percentage: 0,
				size: 0,
			},
			Phase::State(sync) => sync.progress(),
		}
	}
}

