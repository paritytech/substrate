// Copyright 2018 Parity Technologies (UK) Ltd.
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

use primitives::{
	block::{HeaderHash, ExtrinsicHash}
};

/// Possible extrinsic status events
pub enum Status {
	/// Extrinsic has been finalised in block with given hash.
	Finalised(HeaderHash),
	/// Some state change (perhaps another extrinsic was included) rendered this extrinsic invalid
	Usurped(ExtrinsicHash),
	/// The extrinsic has been broadcast to the given peers
	Broadcast(Vec<String>),
}

/// Extrinsic watcher.
///
/// Represents a stream of status updates for particular extrinsic.
pub struct Watcher;

impl Watcher {
	pub fn new() -> Self {
		Watcher
	}

	/// Some state change (perhaps another extrinsic was included) rendered this extrinsic invalid
	pub fn usurped(&self, hash: ExtrinsicHash) {
		unimplemented!()
	}
}
