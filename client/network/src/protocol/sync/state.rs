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
use codec::Encode;
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use sc_client_api::StorageProof;
use crate::schema::v1::{StateRequest, StateResponse, StateEntry};
use crate::chain::{Client, ImportedState};

/// State sync state machine. Accumulates partial state data until it
/// is ready to be imported.
pub struct StateSync<B: BlockT> {
	target_block: B::Hash,
	target_header: B::Header,
	target_root: B::Hash,
	last_key: Vec<u8>,
	state: Vec<(Vec<u8>, Vec<u8>)>,
	complete: bool,
	client: Arc<dyn Client<B>>,
	imported_bytes: u64,
	request_proof: bool,
}

/// Import state chunk result.
pub enum ImportResult<B: BlockT> {
	/// State is complete and ready for import.
	Import(B::Hash, B::Header, ImportedState<B>),
	/// Continue dowloading.
	Continue(StateRequest),
	/// Bad state chunk.
	BadResponse,
}

impl<B: BlockT> StateSync<B> {
	///  Create a new instance.
	pub fn new(client: Arc<dyn Client<B>>, target: B::Header, request_proof: bool) -> Self {
		StateSync {
			client,
			target_block: target.hash(),
			target_root: target.state_root().clone(),
			target_header: target,
			last_key: Vec::default(),
			state: Vec::default(),
			complete: false,
			imported_bytes: 0,
			request_proof,
		}
	}

	///  Validate and import a state reponse.
	pub fn import(&mut self, response: StateResponse) -> ImportResult<B> {
		if response.entries.is_empty() && response.proof.is_empty() && !response.complete {
			log::debug!(
				target: "sync",
				"Bad state response",
			);
			return ImportResult::BadResponse;
		}
		if self.request_proof && response.proof.is_empty() {
			log::debug!(
				target: "sync",
				"Missing proof",
			);
			return ImportResult::BadResponse;
		}
		let complete = if self.request_proof {
			log::debug!(
				target: "sync",
				"Importing state from {} trie nodes",
				response.proof.len(),
			);
			let proof_size = response.proof.iter().map(|v| v.len()).sum::<usize>() as u64;
			let values = match self.client.verify_read_proof(
				self.target_root,
				StorageProof::new(response.proof),
				&self.last_key
			) {
				Err(e) => {
					log::debug!(
						target: "sync",
						"StateResponse failed proof verification: {:?}",
						e,
					);
					return ImportResult::BadResponse;
				},
				Ok(values) => values,
			};
			log::debug!(target: "sync", "Imported with {} keys", values.len());

			if let Some(last) = values.last().map(|(k, _)| k) {
				self.last_key = last.clone();
			}
			let complete = !values.is_empty();

			for (key, value) in values {
				self.imported_bytes += key.len() as u64;
				self.state.push((key, value))
			};
			self.imported_bytes += proof_size;
			complete
		} else {
			log::debug!(
				target: "sync",
				"Importing state from {:?} to {:?}",
				response.entries.last().map(|e| sp_core::hexdisplay::HexDisplay::from(&e.key)),
				response.entries.first().map(|e| sp_core::hexdisplay::HexDisplay::from(&e.key)),
			);

			if let Some(e) = response.entries.last() {
				self.last_key = e.key.clone();
			}
			for StateEntry { key, value } in response.entries {
				self.imported_bytes += (key.len() + value.len()) as u64;
				self.state.push((key, value))
			}
			response.complete
		};
		if complete {
			self.complete = true;
			ImportResult::Import(self.target_block.clone(), self.target_header.clone(), ImportedState {
				block: self.target_block.clone(),
				state: std::mem::take(&mut self.state)
			})
		} else {
			ImportResult::Continue(self.next_request())
		}
	}

	/// Produce next state request.
	pub fn next_request(&self) -> StateRequest {
		StateRequest {
			block: self.target_block.encode(),
			start: self.last_key.clone(),
			with_proof: self.request_proof,
		}
	}

	/// Check if the state is complete.
	pub fn is_complete(&self) -> bool {
		self.complete
	}

	/// Returns target block number.
	pub fn target_block_num(&self) -> NumberFor<B> {
		self.target_header.number().clone()
	}

	/// Returns target block hash.
	pub fn target(&self) -> B::Hash {
		self.target_block.clone()
	}

	/// Returns state sync estimated progress (percentage, bytes)
	pub fn progress(&self) -> (u32, u64) {
		let percent_done = (*self.last_key.get(0).unwrap_or(&0u8) as u32) * 100 / 256;
		(percent_done, self.imported_bytes)
	}
}

