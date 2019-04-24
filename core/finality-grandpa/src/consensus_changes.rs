// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
use std::sync::Arc;
use parity_codec::{Encode, Decode};

/// Consensus-related data changes tracker.
#[derive(Clone, Debug, Encode, Decode)]
pub(crate) struct ConsensusChanges<H, N> {
	pending_changes: Vec<(N, H)>,
}

impl<H, N> ConsensusChanges<H, N> {
	/// Create empty consensus changes.
	pub(crate) fn empty() -> Self {
		ConsensusChanges { pending_changes: Vec::new(), }
	}
}

impl<H: Copy + PartialEq, N: Copy + Ord> ConsensusChanges<H, N> {

	/// Note unfinalized change of consensus-related data.
	pub(crate) fn note_change(&mut self, at: (N, H)) {
		let idx = self.pending_changes
			.binary_search_by_key(&at.0, |change| change.0)
			.unwrap_or_else(|i| i);
		self.pending_changes.insert(idx, at);
	}

	/// Finalize all pending consensus changes that are finalized by given block.
	/// Returns true if there any changes were finalized.
	pub(crate) fn finalize<F: Fn(N) -> ::client::error::Result<Option<H>>>(
		&mut self,
		block: (N, H),
		canonical_at_height: F,
	) -> ::client::error::Result<(bool, bool)> {
		let (split_idx, has_finalized_changes) = self.pending_changes.iter()
			.enumerate()
			.take_while(|(_, &(at_height, _))| at_height <= block.0)
			.fold((None, Ok(false)), |(_, has_finalized_changes), (idx, ref at)|
				(
					Some(idx),
					has_finalized_changes
						.and_then(|has_finalized_changes| if has_finalized_changes {
							Ok(has_finalized_changes)
						} else {
							canonical_at_height(at.0).map(|can_hash| Some(at.1) == can_hash)
						}),
				));

		let altered_changes = split_idx.is_some();
		if let Some(split_idx) = split_idx {
			self.pending_changes = self.pending_changes.split_off(split_idx + 1);
		}
		has_finalized_changes.map(|has_finalized_changes| (altered_changes, has_finalized_changes))
	}
}

/// Thread-safe consensus changes tracker reference.
pub(crate) type SharedConsensusChanges<H, N> = Arc<parking_lot::Mutex<ConsensusChanges<H, N>>>;
