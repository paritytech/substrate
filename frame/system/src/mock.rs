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

//! Test utilities

use sp_core::{
	crypto::KeyTypeId,
	sr25519::Signature,
};
use sp_runtime::{MultiSigner, MultiSignature};
use crate::offchain::AppCrypto;

pub const TEST_KEY_TYPE_ID: KeyTypeId = KeyTypeId(*b"test");

pub mod sr25519 {
	mod app_sr25519 {
		use sp_application_crypto::{app_crypto, sr25519};
		use crate::mock::TEST_KEY_TYPE_ID;
		app_crypto!(sr25519, TEST_KEY_TYPE_ID);
	}

	pub type AuthorityId = app_sr25519::Public;
}

pub struct TestAuthorityId;
impl AppCrypto<MultiSigner, MultiSignature> for TestAuthorityId {
	type RuntimeAppPublic = sr25519::AuthorityId;
	type GenericSignature = Signature;
	type GenericPublic = sp_core::sr25519::Public;
}
