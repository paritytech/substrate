// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate Consensus Common.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Consensus Common is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Consensus Common.  If not, see <http://www.gnu.org/licenses/>.

//! Tracks offline validators.
#![allow(dead_code)]

extern crate substrate_primitives as primitives;
extern crate sr_primitives;

use sr_primitives::{generic::BlockId};
use sr_primitives::traits::{Block, Header};
use sr_primitives::Justification;
use primitives::AuthorityId;

/// Block import trait.
pub trait BlockImport<B: Block> {
	/// Import a block alongside its corresponding justification.
	fn import_block(&self, block: B, justification: Justification, authorities: &[AuthorityId]) -> bool;
}

pub mod offline_tracker;
