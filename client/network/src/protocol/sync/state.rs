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
use codec::{Encode, Decode};
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use sc_client_api::CompactProof;
use crate::schema::v1::{StateRequest, StateResponse, StateEntry};
use crate::chain::{Client, ImportedState};
use smallvec::SmallVec;
use std::collections::HashMap;
use sp_core::storage::well_known_keys;
use super::StateDownloadProgress;

/// State sync support.

/// State sync state machine. Accumulates partial state data until it
/// is ready to be imported.
pub struct StateSync<B: BlockT> {
	target_block: B::Hash,
	target_header: B::Header,
	target_root: B::Hash,
	last_key: SmallVec<[Vec<u8>; 2]>,
	state: HashMap<Vec<Vec<u8>>, Vec<(Vec<u8>, Vec<u8>)>>,
	complete: bool,
	client: Arc<dyn Client<B>>,
	imported_bytes: u64,
	skip_proof: bool,
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
	pub fn new(client: Arc<dyn Client<B>>, target: B::Header, skip_proof: bool) -> Self {
		StateSync {
			client,
			target_block: target.hash(),
			target_root: target.state_root().clone(),
			target_header: target,
			last_key: SmallVec::default(),
			state: HashMap::default(),
			complete: false,
			imported_bytes: 0,
			skip_proof,
		}
	}

	///  Validate and import a state reponse.
	pub fn import(&mut self, response: StateResponse) -> ImportResult<B> {
		if response.entries.is_empty() && response.proof.is_empty() {
			log::debug!(
				target: "sync",
				"Bad state response",
			);
			return ImportResult::BadResponse;
		}
		if !self.skip_proof && response.proof.is_empty() {
			log::debug!(
				target: "sync",
				"Missing proof",
			);
			return ImportResult::BadResponse;
		}
		let complete = if !self.skip_proof {
			log::debug!(
				target: "sync",
				"Importing state from {} trie nodes",
				response.proof.len(),
			);
			let proof_size = response.proof.len() as u64;
			let proof = match CompactProof::decode(&mut response.proof.as_ref()) {
				Ok(proof) => proof,
				Err(e) => {
					log::debug!(target: "sync", "Error decoding proof: {:?}", e);
					return ImportResult::BadResponse;
				}
			};
			let (values, completed) = match self.client.verify_range_proof(
				self.target_root,
				proof,
				self.last_key.as_slice(),
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

			let complete = completed == 0;
			if !complete && !values.update_last_key(completed, &mut self.last_key) {
				log::debug!(target: "sync", "Error updating key cursor, depth: {}", completed);
			};

			for values in values.0 {
				use std::collections::hash_map::Entry;
				let key_values = if values.parent_storages.len() == 0 {
					// skip all child key root (will be recalculated on import)
					values.key_values.into_iter()
						.filter(|key_value| !well_known_keys::is_child_storage_key(key_value.0.as_slice()))
						.collect()
				} else {
					values.key_values
				};
				match self.state.entry(values.parent_storages) {
					Entry::Occupied(mut entry) => {
						for (key, value) in key_values {
							self.imported_bytes += key.len() as u64;
							entry.get_mut().push((key, value))
						}
					},
					Entry::Vacant(entry) => {
						for (key, _value) in key_values.iter() {
							self.imported_bytes += key.len() as u64;
						}
						entry.insert(key_values);
					},
				}
			}
			self.imported_bytes += proof_size;
			complete
		} else {
			let mut complete = true;
			if self.last_key.len() == 2 && response.entries[0].entries.len() == 0 {
				// Unchanged parent trie key, keep old value.
				self.last_key.pop();
			} else {
				self.last_key.clear();
			}
			for state in response.entries {
				log::debug!(
					target: "sync",
					"Importing state from {:?} to {:?}",
					state.entries.last().map(|e| sp_core::hexdisplay::HexDisplay::from(&e.key)),
					state.entries.first().map(|e| sp_core::hexdisplay::HexDisplay::from(&e.key)),
				);

				if !state.complete {
					if let Some(e) = state.entries.last() {
						self.last_key.push(e.key.clone());
					}
					complete = false;
				}
				let is_top = state.parent_storages.len() == 0;
				let entry = self.state.entry(state.parent_storages).or_default();
				for StateEntry { key, value } in state.entries {
					// Skip all child key root (will be recalculated on import).
					if !(is_top && well_known_keys::is_child_storage_key(key.as_slice())) {
						self.imported_bytes += key.len() as u64;
						entry.push((key, value))
					}
				}
			}
			complete
		};
		if complete {
			self.complete = true;
			ImportResult::Import(self.target_block.clone(), self.target_header.clone(), ImportedState {
				block: self.target_block.clone(),
				state: std::mem::take(&mut self.state).into(),
			})
		} else {
			ImportResult::Continue(self.next_request())
		}
	}

	/// Produce next state request.
	pub fn next_request(&self) -> StateRequest {
		StateRequest {
			block: self.target_block.encode(),
			start: self.last_key.clone().into_vec(),
			no_proof: self.skip_proof,
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

	/// Returns state sync estimated progress.
	pub fn progress(&self) -> StateDownloadProgress {
		let cursor = *self.last_key.get(0).and_then(|last| last.get(0)).unwrap_or(&0u8);
		let percent_done =  cursor as u32 * 100 / 256;
		StateDownloadProgress {
			percentage: percent_done,
			size: self.imported_bytes,
		}
	}
}
