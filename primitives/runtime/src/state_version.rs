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

pub use sp_core::state_version::{StateVersion, DEFAULT_STATE_VERSION};
use crate::traits::{Block, NumberFor};
use sp_std::str::FromStr;
use sp_std::vec::Vec;
use sp_arithmetic::traits::Zero;

/// Multiple versions of state in use for a chain.
#[derive(Clone, Default)]
pub struct StateVersions<B: Block> {
	canonical_states: Vec<(NumberFor<B>, StateVersion)>,
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
	pub fn add(&mut self, (at, conf): (NumberFor<B>, StateVersion)) -> StateVersion {
		let mut insert = Some(0);
		let mut replace = None;
		for (i, (number, _)) in self.canonical_states.iter() {
			if number == &at {
				replace = Some(i);
				break;
			}
			if number > &at {
				break;
			}
			insert = i + 1;
		}
		if let Some(i) = replace {
			self.canonical_states[i] = (at, conf);
		} else if let Some(i) = insert {
			self.canonical_states.insert(i, (at, conf));
		}
	}

	/// Convert from chainspec conf.
	pub fn from_conf<'a, I>(conf: I) -> Option<Self>
		where I: IntoIterator<Item = (&'a str, StateVersion)>,
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
		Some(StateVersions {
			canonical_states,
		})
	}
}
