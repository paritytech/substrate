// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use std::sync::Arc;
use parity_scale_codec::{Encode, Decode};

// Tracks authority set changes. We store the block numbers for the last block of each authority
// set.
#[derive(Debug, Encode, Decode)]
pub(crate) struct AuthoritySetChanges<N> {
    authority_set_changes: Vec<N>,
}

impl<N> AuthoritySetChanges<N> {
    pub(crate) fn empty() -> Self {
        Self {
            authority_set_changes: Vec::new(),
        }
	}

	pub(crate) fn append(&mut self, number: N) {
		self.authority_set_changes.push(number)
	}
}

pub(crate) type SharedAuthoritySetChanges<N> = Arc<parking_lot::Mutex<AuthoritySetChanges<N>>>;
