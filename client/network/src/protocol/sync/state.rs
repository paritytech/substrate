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
use crate::schema::v1::{StateRequest, StateResponse};
use crate::chain::{Client, ImportedState};

pub struct StateSync<B: BlockT> {
	target_block: B::Hash,
	target_header: B::Header,
	target_root: B::Hash,
	last_key: Vec<u8>,
	state: Vec<(Vec<u8>, Vec<u8>)>,
	complete: bool,
	client: Arc<dyn Client<B>>,
	imported_bytes: u64,
}

pub enum ImportResult<B: BlockT> {
	Import(B::Hash, B::Header, ImportedState<B>),
	Continue(StateRequest),
	Bad,
}

impl<B: BlockT> StateSync<B> {
	pub fn new(client: Arc<dyn Client<B>>, target: B::Header) -> Self {
		StateSync {
			client,
			target_block: target.hash(),
			target_root: target.state_root().clone(),
			target_header: target,
			last_key: Vec::default(),
			state: Vec::default(),
			complete: false,
			imported_bytes: 0,
		}
	}

	pub fn import(&mut self, response: StateResponse) -> ImportResult<B> {
		if response.keys.is_empty() && !response.complete {
			log::debug!(
				target: "sync",
				"Bad state response",
			);
			return ImportResult::Bad;
		}
		if let Some(key) = response.keys.last() {
			self.last_key = key.clone();
		}
		let proof_size = response.proof.iter().map(|v| v.len()).sum::<usize>() as u64;
		log::trace!(
			target: "sync",
			"Importing state {} bytes, {:?} to {:?}",
			proof_size,
			sp_core::hexdisplay::HexDisplay::from(&self.last_key),
			response.keys.first().map(sp_core::hexdisplay::HexDisplay::from),
		);

		let values = match self.client.verify_proof(
			&response.keys,
			self.target_root,
			StorageProof::new(response.proof),
		) {
			Err(e) => {
				log::debug!(
					target: "sync",
					"StateResponse failed proof verification: {:?}",
					e,
				);
				return ImportResult::Bad;
			},
			Ok(values) => values,
		};

		for (key, value) in values {
			if let Some(value) = value {
				self.imported_bytes += key.len() as u64;
				self.state.push((key, value))
			}
		};
		self.imported_bytes += proof_size;
		if response.complete {
			self.complete = true;
			ImportResult::Import(self.target_block.clone(), self.target_header.clone(), ImportedState {
				block: self.target_block.clone(),
				state: std::mem::take(&mut self.state)
			})
		} else {
			ImportResult::Continue(self.next_request())
		}
	}

	pub fn next_request(&self) -> StateRequest {
		StateRequest {
			block: self.target_block.encode(),
			start: self.last_key.clone(),
		}
	}

	pub fn is_complete(&self) -> bool {
		self.complete
	}

	pub fn target_block_num(&self) -> NumberFor<B> {
		self.target_header.number().clone()
	}

	pub fn target(&self) -> B::Hash {
		self.target_block.clone()
	}

	pub fn progress(&self) -> (u32, u64) {
		let percent_done = (*self.last_key.get(0).unwrap_or(&0u8) as u32) * 100 / 256;
		(percent_done, self.imported_bytes)
	}
}

