// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Support code for the runtime. A set of test accounts.

/// Test account crypto for sr25519.
pub mod sr25519;

/// Test account crypto for ed25519.
pub mod ed25519;

/// Convenience export: Sr25519's Keyring is exposed as `AccountKeyring`,
/// since it tends to be used for accounts.
pub use sr25519::Keyring as AccountKeyring;

/// Convenience export: Ed25519's Keyring is exposed as `AuthorityKeyring`,
/// since it tends to be used for authorities (session keys &c.).
pub use ed25519::Keyring as AuthorityKeyring;

pub mod test {
	/// The keyring for use with accounts when using the test runtime.
	pub use super::ed25519::Keyring as AccountKeyring;
}
