// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use sp_core::{ecdsa, ed25519, sr25519};
use sp_runtime_interface::runtime_interface;

#[runtime_interface]
trait Crypto {
	fn ecdsa_verify(_sig: &ecdsa::Signature, _msg: &[u8], _pub_key: &ecdsa::Public) -> bool {
		true
	}

	#[version(2)]
	fn ecdsa_verify(_sig: &ecdsa::Signature, _msg: &[u8], _pub_key: &ecdsa::Public) -> bool {
		true
	}

	fn ed25519_verify(_sig: &ed25519::Signature, _msg: &[u8], _pub_key: &ed25519::Public) -> bool {
		true
	}

	fn sr25519_verify(_sig: &sr25519::Signature, _msg: &[u8], _pub_key: &sr25519::Public) -> bool {
		true
	}

	#[version(2)]
	fn sr25519_verify(_sig: &sr25519::Signature, _msg: &[u8], _pub_key: &sr25519::Public) -> bool {
		true
	}
}

/// Provides host functions that overrides runtime signature verification
/// to always return true.
pub type SignatureVerificationOverride = crypto::HostFunctions;

// This is here to get rid of the warnings.
#[allow(unused_imports, dead_code)]
use self::crypto::{ecdsa_verify, ed25519_verify, sr25519_verify};
