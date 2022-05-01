// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Migration types for session changes.

use crate::{Session, SessionChanges, PersistedSession, PersistedSessionHeader};
use codec::{Decode, Encode};
use fork_tree::ForkTree;
use sp_runtime::traits::{Block as BlockT, NumberFor};
use std::collections::BTreeMap;

/// Legacy definition of session changes.
#[derive(Clone, Encode, Decode)]
pub struct SessionChangesV0<Hash, Number, E: Session> {
	inner: ForkTree<Hash, Number, PersistedSession<E>>,
}

/// Legacy definition of session changes.
#[derive(Clone, Encode, Decode)]
pub struct SessionChangesV1<Hash, Number, E: Session> {
	inner: ForkTree<Hash, Number, PersistedSessionHeader<E>>,
	sessions: BTreeMap<(Hash, Number), PersistedSession<E>>,
}

/// Type alias for v0 definition of session changes.
pub type SessionChangesV0For<Block, Session> =
	SessionChangesV0<<Block as BlockT>::Hash, NumberFor<Block>, Session>;
/// Type alias for v1 and v2 definition of session changes.
pub type SessionChangesV1For<Block, Session> =
	SessionChangesV1<<Block as BlockT>::Hash, NumberFor<Block>, Session>;

impl<Hash, Number, E: Session> SessionChangesV0<Hash, Number, E>
where
	Hash: PartialEq + Ord + Copy,
	Number: Ord + Copy,
{
	/// Create a new value of this type from raw.
	pub fn from_raw(inner: ForkTree<Hash, Number, PersistedSession<E>>) -> Self {
		Self { inner }
	}

	/// Migrate the type into current session changes definition.
	pub fn migrate(self) -> SessionChanges<Hash, Number, E> {
		let mut sessions = BTreeMap::new();

		let inner = self.inner.map(&mut |hash, number, data| {
			let header = PersistedSessionHeader::from(&data);
			sessions.insert((*hash, *number), data);
			header
		});

		SessionChanges { inner, sessions, gap: None }
	}
}

impl<Hash, Number, E: Session> SessionChangesV1<Hash, Number, E>
where
	Hash: PartialEq + Ord + Copy,
	Number: Ord + Copy,
{
	/// Migrate the type into current session changes definition.
	pub fn migrate(self) -> SessionChanges<Hash, Number, E> {
		SessionChanges { inner: self.inner, sessions: self.sessions, gap: None }
	}
}
