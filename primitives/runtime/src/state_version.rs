// This file is part of Substrate.

// Copyright (C) 2021-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Substrate state versioning and migrations related types.

use crate::traits::{Block, NumberFor};
use crate::generic::{Digest, DigestItem};
use codec::{Decode, Encode};
use sp_arithmetic::traits::Zero;
pub use sp_core::state_version::{StateVersion, DEFAULT_STATE_VERSION};
use sp_std::{str::FromStr, vec::Vec};

/// Multiple versions of state in use for a chain.
#[derive(Clone, crate::RuntimeDebug)]
pub struct StateVersions<B: Block> {
	canonical_states: Vec<(NumberFor<B>, StateVersion)>,
}

impl<B: Block> Default for StateVersions<B> {
	fn default() -> Self {
		StateVersions { canonical_states: Vec::new() }
	}
}

/// Different block specific migrate and state
/// behavior. This is read from chainspec and
/// header block digest.
pub enum MigrateState<H> {
	/// Use current define state version.
	None(StateVersion),
	/// Use state root from digest log.
	Switch(StateVersion, H),
	/// Start migrate between two version.
	Start(StateVersion, StateVersion),
	/// Pending migration between two version
	/// with pending root of destination version.
	Pending(StateVersion, StateVersion, H),
}

/// Error related to migration digest from parent block header
/// and on import current block header.
pub enum InvalidErrorDigest {
	/// Parent migrate do not match chainspec digest declaration.
	InvalidParent,
	/// Missing digest in parent header when expected.
	MissingParentDigest,
	/// Parent migrate switch to a state different than current one.
	/// This is a bug.
	InvalidParentSwitchState,
	/// Imported digest do not match chainspec declaration.
	InvalidImportedHeaderDigest,
}

#[cfg(feature = "std")]
impl std::fmt::Display for InvalidErrorDigest {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		let msg = " TODO implement with comments";
		write!(f, "{}", msg)
	}
}

impl<B: Block> StateVersions<B> {
	/// Access genesis state version.
	/// This uses default state if undefined.
	pub fn genesis_state_version(&self) -> StateVersion {
		if let Some((number, version)) = self.canonical_states.get(0) {
			if number.is_zero() {
				return *version;
			}
		}
		DEFAULT_STATE_VERSION
	}

	/// Resolve state version for a given
	/// block height.
	pub fn state_version_at(&self, at: NumberFor<B>) -> StateVersion {
		let mut version = DEFAULT_STATE_VERSION;
		for (number, state) in self.canonical_states.iter() {
			if number > &at {
				break;
			}
			version = *state;
		}
		version
	}

	/// Modify configuration, mostly for testing.
	pub fn add(&mut self, (at, conf): (NumberFor<B>, StateVersion)) {
		let mut insert = Some(0);
		let mut replace = None;
		for (i, (number, _)) in self.canonical_states.iter().enumerate() {
			if number == &at {
				replace = Some(i);
				break;
			}
			if number > &at {
				break;
			}
			insert = Some(i + 1);
		}
		if let Some(i) = replace {
			self.canonical_states[i] = (at, conf);
		} else if let Some(i) = insert {
			self.canonical_states.insert(i, (at, conf));
		}
	}

	/// Convert from chainspec conf.
	pub fn from_conf<'a, I>(conf: I) -> Option<Self>
	where
		I: IntoIterator<Item = (&'a str, StateVersion)>,
	{
		let iter = conf.into_iter();
		let mut canonical_states = match iter.size_hint() {
			(s, None) => Vec::with_capacity(s),
			(_, Some(s)) => Vec::with_capacity(s),
		};

		for (number, version) in iter {
			if let Ok(number) = NumberFor::<B>::from_str(number) {
				canonical_states.push((number.into(), version));
			} else {
				return None;
			}
		}
		Some(StateVersions { canonical_states })
	}

	/// Indicate if block need migration.
	/// Returns version to migrate from and to if
	/// migration is needed.
	pub fn need_migrate(&self, at: NumberFor<B>) -> Option<(StateVersion, StateVersion)> {
		let (from, to, _) = self.need_migrate_inner(at);
		to.map(|to| (from, to))
	}

	fn need_migrate_inner(&self, at: NumberFor<B>) -> (StateVersion, Option<StateVersion>, bool) {
		// TODO switch to default when all V0 chains did migrate.
		let mut from = StateVersion::V0;
		let mut to = None;
		let mut first = true;
		let at_plus_one = at + 1u32.into();
		for (number, version) in self.canonical_states.iter() {
			first = number == &at;
			if number == &at_plus_one {
				to = Some(*version);
				break;
			}
			if number > &at_plus_one {
				break;
			}
			from = *version;
		}
		(from, to, first)
	}

	/// TODO remove pub and replace by resolve_migrate (and cache result).
	pub fn migrate_digest(digests: &Digest<B::Hash>) -> Option<&StateMigrationDigest<B::Hash>> {
		digests.log(|digest| if let DigestItem::StateMigration(digest) = digest {
			Some(digest)
		} else {
			None
		})
	}

	/// Push or update migration digest.
	pub fn set_migrate_digest(digests: &mut Digest<B::Hash>, migration_digest: StateMigrationDigest<B::Hash>) {
		for digest in digests.logs.iter_mut() {
			if let DigestItem::StateMigration(digest) = digest {
				*digest = migration_digest;
				return
			}
		}
		digests.logs.push(DigestItem::StateMigration(migration_digest));
	}

	/// Get migration specific block behavior.
	pub fn resolve_migrate(
		&self,
		at: NumberFor<B>,
		parent_digests: &Digest<B::Hash>,
		imported_block_digests: Option<&Digest<B::Hash>>,
	) -> Result<MigrateState<B::Hash>, InvalidErrorDigest> {
		if at.is_zero() {
			// No migration at genesis (a bit useless since parent
			// digest is undefiend, but one could use default).
			// So ignoring input digest could also error.
			return Ok(MigrateState::None(self.state_version_at(at)));
		}
		match self.need_migrate_inner(at) {
			(from, Some(to), false) => {
				// no migration digest allowed (only start at chainspec -1 and
				// no consecutive mig support). and no from runtime trigger.
				if Self::migrate_digest(parent_digests).is_some() {
					return Err(InvalidErrorDigest::InvalidParent);
				}


				if let Some(digests) = imported_block_digests {
					if Self::migrate_digest(digests).is_some() {
						return Err(InvalidErrorDigest::InvalidImportedHeaderDigest);
					}
				}
				Ok(MigrateState::Start(from, to))
			},
			(from, None, true) => {
				// switch
				let state_root = if let Some(digest) = Self::migrate_digest(parent_digests) {
					match digest {
						StateMigrationDigest { to, state_root, progress: StateMigrationProgress::Finished, .. } => {
							if to != &from {
								return Err(InvalidErrorDigest::InvalidParentSwitchState);
							}
							state_root
						},
/*						_ => {
							return Err(InvalidErrorDigest::InvalidParent);
						},*/
					}
				} else {
					return Err(InvalidErrorDigest::MissingParentDigest);
				};

				if let Some(digests) = imported_block_digests {
					// No support for consecutive migrations.
					if Self::migrate_digest(digests).is_some() {
						return Err(InvalidErrorDigest::InvalidImportedHeaderDigest);
					}
				}

				Ok(MigrateState::Switch(from, state_root.clone()))
			},
			(from, None, false) => {
				if Self::migrate_digest(parent_digests).is_some() {
					return Err(InvalidErrorDigest::InvalidParent);
				}

				if let Some(digests) = imported_block_digests {
					// current digest need to be nothing TODO later could migrate from runtime trigger?
					if Self::migrate_digest(digests).is_some() {
						return Err(InvalidErrorDigest::InvalidImportedHeaderDigest);
					}
				}
				Ok(MigrateState::None(from))
			},
			(_, Some(_), true) => unreachable!("need_migrate_inner exclude target block from migration range"),
		}

	}
}

/// Migration definition at a given block.
#[derive(PartialEq, Eq, Clone, crate::RuntimeDebug, Encode, Decode)]
#[cfg_attr(feature = "std", derive(parity_util_mem::MallocSizeOf))]
pub struct StateMigrationDigest<Hash> {
	/// State version to double check.
	pub from: StateVersion,
	/// State version to double check.
	pub to: StateVersion,
	/// State root of target state.
	pub state_root: Hash,
	/// Current state.
	pub progress: StateMigrationProgress,
}

/// State of migration for a given block.
#[derive(PartialEq, Eq, Clone, crate::RuntimeDebug, Encode, Decode)]
#[cfg_attr(feature = "std", derive(parity_util_mem::MallocSizeOf))]
pub enum StateMigrationProgress {
	// Started, start requested from runtime (field `StateMigrationDigest` other than `to` should be ignored),
	// then we switch the digest to `Pending` for empty state root and correct version.

	// Pending, read progress from destination at well known key
	// (need to overwrite with origin value when finish).

	//
	/// Destination is equivalent to origin.
	///
	/// Next block will use `to` state with the
	/// state root of from the migration progress destination state.
	Finished,
}
