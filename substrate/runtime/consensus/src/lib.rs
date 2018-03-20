// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Conensus module for runtime; manages the authority set ready for the native code.

#![cfg_attr(not(feature = "std"), no_std)]

#[allow(unused_imports)] #[macro_use] extern crate substrate_runtime_std as rstd;
#[macro_use] extern crate substrate_runtime_support as runtime_support;

#[cfg(feature = "std")] #[macro_use] extern crate serde_derive;
#[cfg(feature = "std")] extern crate serde;

use rstd::prelude::*;
use runtime_support::storage;
use runtime_support::storage::unhashed::StorageVec;
use runtime_support::dispatch::PrivPass;

pub type SessionKey = [u8; 32];

pub const AUTHORITY_AT: &'static[u8] = b":auth:";
pub const AUTHORITY_COUNT: &'static[u8] = b":auth:len";

struct AuthorityStorageVec {}
impl StorageVec for AuthorityStorageVec {
	type Item = SessionKey;
	const PREFIX: &'static[u8] = AUTHORITY_AT;
}

pub const CODE: &'static[u8] = b":code";

/// Get the current set of authorities. These are the session keys.
pub fn authorities() -> Vec<SessionKey> {
	AuthorityStorageVec::items()
}

impl_dispatch! {
	pub mod privileged;
	fn set_code(self, new: Vec<u8>) = 0;
}

impl privileged::Dispatch for PrivPass {
	/// Set the new code.
	fn set_code(self, new: Vec<u8>) {
		internal::set_code(new);
	}
}

pub mod internal {
	use super::*;

	/// Set the new code.
	pub fn set_code(new: Vec<u8>) {
		storage::unhashed::put_raw(CODE, &new);
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
}
