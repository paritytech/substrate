// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

use client;
use primitives::{block, parachain};

/// Temporary dummy blockchain implementation for tests.
#[derive(Debug, Default)]
pub struct Blockchain;

impl client::Blockchain for Blockchain {
	type Error = ::std::io::Error;

	fn latest_hash(&self) -> Result<block::HeaderHash, Self::Error> {
		Ok(0.into())
	}

	fn header(&self, hash: &block::HeaderHash) -> Result<Option<block::Header>, Self::Error> {
		Ok(if hash != &0.into() {
			None
		} else {
			Some(block::Header {
				parent_hash: 0.into(),
				number: 0,
				state_root: 0.into(),
				parachain_activity: parachain::Activity(vec![0]),
				logs: vec![],
			})
		})
	}
}

