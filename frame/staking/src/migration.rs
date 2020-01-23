// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Storage migrations for srml-staking.

/// Indicator of a version of a storage layout.
pub type VersionNumber = u32;

// the current expected version of the storage
pub const CURRENT_VERSION: VersionNumber = 2;

/// The inner logic of migrations.
#[cfg(any(test, feature = "migrate"))]
pub mod inner {
	use crate::{Store, Module, Trait};
	use frame_support::{StorageLinkedMap, StoragePrefixedMap, StorageValue};
	use codec::{Encode, Decode};
	use sp_std::vec::Vec;
	use super::{CURRENT_VERSION, VersionNumber};

	// the minimum supported version of the migration logic.
	const MIN_SUPPORTED_VERSION: VersionNumber = 0;

	// migrate storage from v0 to v1.
	//
	// this upgrades the `Nominators` linked_map value type from `Vec<T::AccountId>` to
	// `Option<Nominations<T::AccountId>>`
	pub fn to_v1<T: Trait>(version: &mut VersionNumber) {
		if *version != 0 { return }
		*version += 1;

		let now = <Module<T>>::current_era();
		let res = <Module<T> as Store>::Nominators::translate::<T::AccountId, Vec<T::AccountId>, _, _>(
			|key| key,
			|targets| crate::Nominations {
				targets,
				submitted_in: now,
				suppressed: false,
			},
		);

		if let Err(e) = res {
			frame_support::print("Encountered error in migration of Staking::Nominators map.");
			if e.is_none() {
				frame_support::print("Staking::Nominators map reinitialized");
			}
		}

		frame_support::print("Finished migrating Staking storage to v1.");
	}

	// migrate storage from v1 to v2: adds another field to the `SlashingSpans`
	// struct.
	pub fn to_v2<T: Trait>(version: &mut VersionNumber) {
		use crate::{EraIndex, slashing::SpanIndex};
		#[derive(Decode)]
		struct V1SlashingSpans {
			span_index: SpanIndex,
			last_start: EraIndex,
			prior: Vec<EraIndex>,
		}

		#[derive(Encode)]
		struct V2SlashingSpans {
			span_index: SpanIndex,
			last_start: EraIndex,
			last_nonzero_slash: EraIndex,
			prior: Vec<EraIndex>,
		}

		if *version != 1 { return }
		*version += 1;

		let prefix = <Module<T> as Store>::SlashingSpans::final_prefix();
		let mut current_key = prefix.to_vec();
		loop {
			let maybe_next_key = sp_io::storage::next_key(&current_key[..])
				.filter(|v| v.starts_with(&prefix[..]));

			match maybe_next_key {
				Some(next_key) => {
					let maybe_spans = sp_io::storage::get(&next_key[..])
						.and_then(|v| V1SlashingSpans::decode(&mut &v[..]).ok());
					if let Some(spans) = maybe_spans {
						let new_val = V2SlashingSpans {
							span_index: spans.span_index,
							last_start: spans.last_start,
							last_nonzero_slash: spans.last_start,
							prior: spans.prior,
						}.encode();

						sp_io::storage::set(&next_key[..], &new_val[..]);
					}
					current_key = next_key;
				}
				None => break,
			}
		}
	}

	pub(super) fn perform_migrations<T: Trait>() {
		<Module<T> as Store>::StorageVersion::mutate(|version| {
			if *version < MIN_SUPPORTED_VERSION {
				frame_support::print("Cannot migrate staking storage because version is less than\
					minimum.");
				frame_support::print(*version);
				return
			}

			if *version == CURRENT_VERSION { return }

			to_v1::<T>(version);
			to_v2::<T>(version);
		});
	}
}

#[cfg(not(any(test, feature = "migrate")))]
mod inner {
	pub(super) fn perform_migrations<T>() { }
}

/// Perform all necessary storage migrations to get storage into the expected stsate for current
/// logic. No-op if fully upgraded.
pub(crate) fn perform_migrations<T: crate::Trait>() {
	inner::perform_migrations::<T>();
}
