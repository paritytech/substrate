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

use codec::Encode;
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use crate::schema::v1::{StateRequest, StateResponse, StateEntry};
use crate::chain::ImportedState;

pub struct StateSync<B: BlockT> {
	target_block: B::Hash,
	target_header: B::Header,
	target_root: B::Hash,
	last_key: Vec<u8>,
	state: Vec<(Vec<u8>, Vec<u8>)>,
}

pub enum ImportResult<B: BlockT> {
	Import(B::Hash, B::Header, ImportedState<B>),
	Continue(StateRequest),
	Bad,
}

impl<B: BlockT> StateSync<B> {
	pub fn new(target: &B::Header) -> Self {
		StateSync {
			target_block: target.hash(),
			target_root: target.state_root().clone(),
			target_header: target.clone(),
			last_key: Vec::default(),
			state: Vec::default(),
		}
	}

	pub fn import(&mut self, response: StateResponse) -> ImportResult<B> {
		if let Some(StateEntry { key, .. }) = response.values.last() {
			self.last_key = key.clone();
		}
		for StateEntry { key, value } in response.values {
			self.state.push((key, value))
		};
		if response.complete {
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

	pub fn target_block_num(&self) -> NumberFor<B> {
		self.target_header.number().clone()
	}
}

