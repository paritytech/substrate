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

//! Set of helpers used to assist testing in other crates.

use sp_core::{crypto::Public, H256};
use crate::{SharedAuthoritySet, AuthorityId, authorities::AuthoritySet};

/// Construct an example `SharedAuthoritySet` to be used in tests in other crates.
pub fn example_shared_authority_set() -> SharedAuthoritySet<H256, u64> {
	let id = AuthorityId::from_slice(&[42; 32]);
	let auth_set = AuthoritySet::<H256, u64>::genesis(vec![(id, 1)])
		.expect("authority set is explicitly non-empty. qed");
	SharedAuthoritySet::from(auth_set)
}