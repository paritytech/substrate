// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! An opt-in utility for tracking historical sessions in SRML-session.
//!
//! This is generally useful when implementing blockchains that require accountable
//! safety where validators from some amount f prior sessions must remain slashable.
//!
//! Rather than store the full session data for any given session, we instead commit
//! to the roots of merkle tries containing the session data.

use rstd::{prelude::*, marker::PhantomData, ops::Rem};
#[cfg(not(feature = "std"))]
use rstd::alloc::borrow::ToOwned;
use parity_codec::Decode;
use primitives::traits::{Zero, Saturating, Member, OpaqueKeys};
use srml_support::{
	ConsensusEngineId, StorageValue, StorageMap, for_each_tuple, decl_module,
	decl_event, decl_storage,
};
use srml_support::{ensure, traits::{OnFreeBalanceZero, Get, FindAuthor}, Parameter, print};
use system::ensure_signed;
use substrate_trie::{MemoryDB, TrieMut, TrieDBMut, TrieDB};

use super::{Trait, SessionIndex, OnSessionEnding, Module as SessionModule};

decl_storage! {
	trait Store for Module<T: Trait> as Session {
		/// Mapping from historical session indices to session-data root hash.
		HistoricalSessions get(historical_root): map SessionIndex => Option<T::Hash>;
		/// The range of historical sessions we store. [first, last)
		StoredRange: Option<(SessionIndex, SessionIndex)>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin { }
}

impl<T: Trait> Module<T> {
	/// Prune historical stored session roots up to (but not including)
	/// `up_to`.
	pub fn prune_up_to(up_to: SessionIndex) {
		<Self as Store>::StoredRange::mutate(|range| {
			let (start, end) = match *range {
				Some(range) => range,
				None => return, // nothing to prune.
			};

			let up_to = rstd::cmp::min(up_to, end);

			if up_to < start {
				return // out of bounds. harmless.
			}

			for i in start..up_to {
				<Self as Store>::HistoricalSessions::take(i);
			}

			let new_start = up_to;
			*range = if new_start == end {
				None // nothing is stored.
			} else {
				Some((new_start, end))
			}
		})
	}

	/// Generate a session-trie for the current session. This is used for proving
	/// membership of voters.
	///
	/// In general, this should not be used on-chain and instead only in runtime APIs
	/// that need to prove membership of a validator in the current set.
	pub fn generate_proving_trie() -> Result<ProvingTrie<T>, &'static str> {
		ProvingTrie::generate()
	}
}

impl<T: Trait> OnSessionEnding<T::AccountId> for Module<T> {
	fn on_session_ending(i: SessionIndex) -> Option<Vec<T::AccountId>> {
		<Self as Store>::StoredRange::mutate(|range| {
			range.get_or_insert_with(|| (i, i)).1 = i + 1;
		});

		unimplemented!();

		None
	}
}

/// useful for constructing proofs.
pub struct ProvingTrie<T: SessionTrait> {
	db: MemoryDB<T::Hash>,
	root: T::Hash,
}

impl<T: SessionTrait> ProvingTrie<T> {
	fn generate() -> Result<Self, &'static str> {
		let validators = <SessionModule<T>>::validators();
		let n = validators.len();
		ensure!(n <= u32::max_value() as usize, "2^32 or more validators is unsupported");

		let n = n as u32;

		let mut db = MemoryDB::new();
		let mut root: T::Hash = Default::default();
		{
			let mut db = TrieDBMut::new();

			unimplemented!();
		}
	}

	/// Access the underlying trie root.
	pub fn root(&self) -> &T::Hash {
		&self.root
	}
}
