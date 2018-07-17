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

//! Local collations to be circulated to validators.
//!
//! Collations are attempted to be repropagated when a new validator connects,
//! a validator changes his session key, or when they are generated.

use polkadot_primitives::{Hash, Collation};

use std::collations::{HashMap, HashSet};
use std::time::Duration;

const LIVE_FOR: Duration = Duration::from_secs(60 * 5);

/// Actions to take.
pub enum Action {
	SendTo(SessionKey),
}

pub struct LocalCollation {
	targets: HashSet<SessionKey>,
	collation: Collation,
}

pub struct LocalCollations {
	primary_for: HashSet<SessionKey>,
	local_collations: HashMap<Hash, LocalCollation>,
}

impl LocalCollations {
	pub fn new_validator(&mut self) {
		unimplemented!()
	}
}
