// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Runtime Api to help discover authorities.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::vec::Vec;

mod app {
	use sp_application_crypto::{
		key_types::AUTHORITY_DISCOVERY,
		app_crypto,
		sr25519,
	};
	app_crypto!(sr25519, AUTHORITY_DISCOVERY);
}

sp_application_crypto::with_pair! {
	/// An authority discovery authority keypair.
	pub type AuthorityPair = app::Pair;
}

/// An authority discovery authority identifier.
pub type AuthorityId = app::Public;

/// An authority discovery authority signature.
pub type AuthoritySignature = app::Signature;

sp_api::decl_runtime_apis! {
	/// The authority discovery api.
	///
	/// This api is used by the `client/authority-discovery` module to retrieve identifiers
	/// of the current authority set.
	pub trait AuthorityDiscoveryApi {
		/// Retrieve authority identifiers of the current authority set.
		fn authorities() -> Vec<AuthorityId>;
	}
}
