// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Support code for the runtime. A set of test accounts.

/// Test account crypto for sr25519.
pub mod sr25519;

/// Test account crypto for ed25519.
pub mod ed25519;

/// Convenience export: Sr25519's Keyring is exposed as `AccountKeyring`,
/// since it tends to be used for accounts (although it may also be used
/// by authorities).
pub use sr25519::Keyring as AccountKeyring;

pub use ed25519::Keyring as Ed25519Keyring;
pub use sr25519::Keyring as Sr25519Keyring;

pub mod test {
	/// The keyring for use with accounts when using the test runtime.
	pub use super::ed25519::Keyring as AccountKeyring;
}
