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

///! Warp sync support.
use super::state::{ImportResult, StateSync};
use crate::schema::v1::{StateRequest, StateResponse};
pub use crate::warp_request_handler::{
	EncodedProof, Request as WarpProofRequest, VerificationResult, WarpSyncProvider,
};
use sc_client_api::ProofProvider;
use sp_blockchain::HeaderBackend;
use sp_finality_grandpa::{AuthorityList, SetId};
use sp_runtime::traits::{Block as BlockT, NumberFor, Zero};
use std::sync::Arc;

enum Phase<B: BlockT, Client> {
	WarpProof { set_id: SetId, authorities: AuthorityList, last_hash: B::Hash },
	State(StateSync<B, Client>),
}

/// Reported warp sync phase.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum WarpSyncPhase<B: BlockT> {
	/// Waiting for peers to connect.
	AwaitingPeers,
	/// Downloading and verifying grandpa warp proofs.
	DownloadingWarpProofs,
	/// Downloading state data.
	DownloadingState,
	/// Importing state.
	ImportingState,
	/// Downloading block history.
	DownloadingBlocks(NumberFor<B>),
}

/// Reported warp sync progress.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct WarpSyncProgress<B: BlockT> {
	/// Estimated download percentage.
	pub phase: WarpSyncPhase<B>,
	/// Total bytes downloaded so far.
	pub total_bytes: u64,
}

/// Import warp proof result.
pub enum WarpProofImportResult {
	/// Import was successful.
	Success,
	/// Bad proof.
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
			Phase::WarpProof { .. } => {
				log::debug!(target: "sync", "Unexpected state response");
				ImportResult::BadResponse
			},
			Phase::State(sync) => sync.import(response),
		}
	}

	///  Validate and import a warp proof response.
	pub fn import_warp_proof(&mut self, response: EncodedProof) -> WarpProofImportResult {
		match &mut self.phase {
			Phase::State(_) => {
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
						let state_sync = StateSync::new(self.client.clone(), header, false);
						self.phase = Phase::State(state_sync);
						WarpProofImportResult::Success
					},
				}
			},
		}
	}

	/// Produce next state request.
	pub fn next_state_request(&self) -> Option<StateRequest> {
		match &self.phase {
			Phase::WarpProof { .. } => None,
			Phase::State(sync) => Some(sync.next_request()),
		}
	}

	/// Produce next warp proof request.
	pub fn next_warp_poof_request(&self) -> Option<WarpProofRequest<B>> {
		match &self.phase {
			Phase::State(_) => None,
			Phase::WarpProof { last_hash, .. } => Some(WarpProofRequest { begin: *last_hash }),
		}
	}

	/// Return target block hash if it is known.
	pub fn target_block_hash(&self) -> Option<B::Hash> {
		match &self.phase {
			Phase::State(s) => Some(s.target()),
			Phase::WarpProof { .. } => None,
		}
	}

	/// Return target block number if it is known.
	pub fn target_block_number(&self) -> Option<NumberFor<B>> {
		match &self.phase {
			Phase::State(s) => Some(s.target_block_num()),
			Phase::WarpProof { .. } => None,
		}
	}

	/// Check if the state is complete.
	pub fn is_complete(&self) -> bool {
		match &self.phase {
			Phase::WarpProof { .. } => false,
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
