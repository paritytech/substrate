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

//! Conensus module for runtime; manages the authority set ready for the native code.

use runtime_support::Vec;
use storable::StorageVec;
use primitives::SessionKey;

struct AuthorityStorageVec {}
impl StorageVec for AuthorityStorageVec {
	type Item = SessionKey;
	const PREFIX: &'static[u8] = b"con:aut:";
}

/// Get the current set of authorities. These are the session keys.
pub fn authorities() -> Vec<SessionKey> {
	AuthorityStorageVec::items()
}

/// Set the current set of authorities' session keys.
///
/// Called by `next_session` only.
pub fn set_authorities(authorities: &[SessionKey]) {
	AuthorityStorageVec::set_items(authorities);
}

/// Set a single authority by index.
pub fn set_authority(index: u32, key: &SessionKey) {
	AuthorityStorageVec::set_item(index, key);
}
