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

//! Warp sync support.

use crate::{
	schema::v1::{StateRequest, StateResponse},
	state::{ImportResult, StateSync},
};
use sc_client_api::ProofProvider;
use sc_network_common::sync::{
	message::{BlockAttributes, BlockData, BlockRequest, Direction, FromBlock},
	warp::{
		EncodedProof, VerificationResult, WarpProofRequest, WarpSyncPhase, WarpSyncProgress,
		WarpSyncProvider,
	},
};
use sp_blockchain::HeaderBackend;
use sp_finality_grandpa::{AuthorityList, SetId};
use sp_runtime::traits::{Block as BlockT, Header, NumberFor, Zero};
use std::sync::Arc;

enum Phase<B: BlockT, Client> {
	WarpProof { set_id: SetId, authorities: AuthorityList, last_hash: B::Hash },
	TargetBlock(B::Header),
	State(StateSync<B, Client>),
}

/// Import warp proof result.
pub enum WarpProofImportResult {
	/// Import was successful.
	Success,
	/// Bad proof.
	BadResponse,
}

/// Import target block result.
pub enum TargetBlockImportResult {
	/// Import was successful.
	Success,
	/// Invalid block.
	BadResponse,
}

/// Warp sync state machine. Accumulates warp proofs and state.
pub struct WarpSync<B: BlockT, Client> {
	phase: Phase<B, Client>,
	client: Arc<Client>,
	warp_sync_provider: Arc<dyn WarpSyncProvider<B>>,
	total_proof_bytes: u64,
}

impl<B, Client> WarpSync<B, Client>
where
	B: BlockT,
	Client: HeaderBackend<B> + ProofProvider<B> + 'static,
{
	///  Create a new instance.
	pub fn new(client: Arc<Client>, warp_sync_provider: Arc<dyn WarpSyncProvider<B>>) -> Self {
		let last_hash = client.hash(Zero::zero()).unwrap().expect("Genesis header always exists");
		let phase = Phase::WarpProof {
			set_id: 0,
			authorities: warp_sync_provider.current_authorities(),
			last_hash,
		};
		Self { client, warp_sync_provider, phase, total_proof_bytes: 0 }
	}

	///  Validate and import a state response.
	pub fn import_state(&mut self, response: StateResponse) -> ImportResult<B> {
		match &mut self.phase {
			Phase::WarpProof { .. } | Phase::TargetBlock(_) => {
				log::debug!(target: "sync", "Unexpected state response");
				ImportResult::BadResponse
			},
			Phase::State(sync) => sync.import(response),
		}
	}

	///  Validate and import a warp proof response.
	pub fn import_warp_proof(&mut self, response: EncodedProof) -> WarpProofImportResult {
		match &mut self.phase {
			Phase::State(_) | Phase::TargetBlock(_) => {
				log::debug!(target: "sync", "Unexpected warp proof response");
				WarpProofImportResult::BadResponse
			},
			Phase::WarpProof { set_id, authorities, last_hash } => {
				match self.warp_sync_provider.verify(&response, *set_id, authorities.clone()) {
					Err(e) => {
						log::debug!(target: "sync", "Bad warp proof response: {}", e);
						WarpProofImportResult::BadResponse
					},
					Ok(VerificationResult::Partial(new_set_id, new_authorities, new_last_hash)) => {
						log::debug!(target: "sync", "Verified partial proof, set_id={:?}", new_set_id);
						*set_id = new_set_id;
						*authorities = new_authorities;
						*last_hash = new_last_hash;
						self.total_proof_bytes += response.0.len() as u64;
						WarpProofImportResult::Success
					},
					Ok(VerificationResult::Complete(new_set_id, _, header)) => {
						log::debug!(target: "sync", "Verified complete proof, set_id={:?}", new_set_id);
						self.total_proof_bytes += response.0.len() as u64;
						self.phase = Phase::TargetBlock(header);
						WarpProofImportResult::Success
					},
				}
			},
		}
	}

	/// Import the target block body.
	pub fn import_target_block(&mut self, block: BlockData<B>) -> TargetBlockImportResult {
		match &mut self.phase {
			Phase::WarpProof { .. } | Phase::State(_) => {
				log::debug!(target: "sync", "Unexpected target block response");
				TargetBlockImportResult::BadResponse
			},
			Phase::TargetBlock(header) =>
				if let Some(block_header) = &block.header {
					if block_header == header {
						if block.body.is_some() {
							let state_sync = StateSync::new(
								self.client.clone(),
								header.clone(),
								block.body,
								false,
							);
							self.phase = Phase::State(state_sync);
							TargetBlockImportResult::Success
						} else {
							log::debug!(target: "sync", "Importing target block failed: no body.");
							TargetBlockImportResult::BadResponse
						}
					} else {
						log::debug!(
							target: "sync",
							"Importing target block failed: different header.",
						);
						TargetBlockImportResult::BadResponse
					}
				} else {
					log::debug!(target: "sync", "Importing target block failed: no header.");
					TargetBlockImportResult::BadResponse
				},
		}
	}

	/// Produce next state request.
	pub fn next_state_request(&self) -> Option<StateRequest> {
		match &self.phase {
			Phase::WarpProof { .. } => None,
			Phase::TargetBlock(_) => None,
			Phase::State(sync) => Some(sync.next_request()),
		}
	}

	/// Produce next warp proof request.
	pub fn next_warp_proof_request(&self) -> Option<WarpProofRequest<B>> {
		match &self.phase {
			Phase::WarpProof { last_hash, .. } => Some(WarpProofRequest { begin: *last_hash }),
			Phase::TargetBlock(_) => None,
			Phase::State(_) => None,
		}
	}

	/// Produce next target block request.
	pub fn next_target_block_request(&self) -> Option<(NumberFor<B>, BlockRequest<B>)> {
		match &self.phase {
			Phase::WarpProof { .. } => None,
			Phase::TargetBlock(header) => {
				let request = BlockRequest::<B> {
					id: 0,
					fields: BlockAttributes::HEADER | BlockAttributes::BODY,
					from: FromBlock::Hash(header.hash()),
					to: Some(header.hash()),
					direction: Direction::Ascending,
					max: Some(1),
				};
				Some((*header.number(), request))
			},
			Phase::State(_) => None,
		}
	}

	/// Return target block hash if it is known.
	pub fn target_block_hash(&self) -> Option<B::Hash> {
		match &self.phase {
			Phase::WarpProof { .. } => None,
			Phase::TargetBlock(_) => None,
			Phase::State(s) => Some(s.target()),
		}
	}

	/// Return target block number if it is known.
	pub fn target_block_number(&self) -> Option<NumberFor<B>> {
		match &self.phase {
			Phase::WarpProof { .. } => None,
			Phase::TargetBlock(header) => Some(*header.number()),
			Phase::State(s) => Some(s.target_block_num()),
		}
	}

	/// Check if the state is complete.
	pub fn is_complete(&self) -> bool {
		match &self.phase {
			Phase::WarpProof { .. } => false,
			Phase::TargetBlock(_) => false,
			Phase::State(sync) => sync.is_complete(),
		}
	}

	/// Returns state sync estimated progress (percentage, bytes)
	pub fn progress(&self) -> WarpSyncProgress<B> {
		match &self.phase {
			Phase::WarpProof { .. } => WarpSyncProgress {
				phase: WarpSyncPhase::DownloadingWarpProofs,
				total_bytes: self.total_proof_bytes,
			},
			Phase::TargetBlock(_) => WarpSyncProgress {
				phase: WarpSyncPhase::DownloadingTargetBlock,
				total_bytes: self.total_proof_bytes,
			},
			Phase::State(sync) => WarpSyncProgress {
				phase: if self.is_complete() {
					WarpSyncPhase::ImportingState
				} else {
					WarpSyncPhase::DownloadingState
				},
				total_bytes: self.total_proof_bytes + sync.progress().size,
			},
		}
	}
}
