// Copyright 2020 Parity Technologies (UK) Ltd.
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

use parity_scale_codec::{Decode, Encode};
use std::{cmp::Ord, sync::Arc};

// Tracks authority set changes. We store the block numbers for the last block of each authority
// set.
#[derive(Debug, Encode, Decode)]
pub(crate) struct AuthoritySetChanges<N> {
    authority_set_changes: Vec<N>,
}

impl<N: Ord + Copy> AuthoritySetChanges<N> {
    pub(crate) fn empty() -> Self {
        Self {
            authority_set_changes: Vec::new(),
        }
    }

    pub(crate) fn append(&mut self, number: N) {
        self.authority_set_changes.push(number)
    }

    pub(crate) fn get_set_id(&self, number: N) -> (u64, N) {
        let set_id = self
            .authority_set_changes
            .binary_search(&number)
            .unwrap_or_else(|idx| idx);
        let last_block_for_set_id = self.authority_set_changes[set_id];
        // WIP: avoid cast?
        (set_id as u64, last_block_for_set_id)
    }
}

pub(crate) type SharedAuthoritySetChanges<N> = Arc<parking_lot::Mutex<AuthoritySetChanges<N>>>;
