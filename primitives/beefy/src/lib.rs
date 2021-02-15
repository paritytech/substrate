// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]
// NOTE: needed to silence warnings about generated code in `decl_runtime_apis`
#![allow(clippy::too_many_arguments, clippy::unnecessary_mut_passed)]

//! Primitives for BEEFY protocol.
//!
//! The crate contains shared data types used by BEEFY protocol and documentation (in a form of
//! code) for building a BEEFY light client.
//!
//! BEEFY is a gadget that runs alongside another finality gadget (for instance GRANDPA).
//! For simplicity (and the initially intended use case) the documentation says GRANDPA in places
//! where a more abstract "Finality Gadget" term could be used, but there is no reason why BEEFY
//! wouldn't run with some other finality scheme.
//! BEEFY validator set is supposed to be tracking the Finality Gadget validator set, but note that
//! it will use a different set of keys. For Polkadot use case we plan to use `secp256k1` for BEEFY,
//! while GRANDPA uses `ed25519`.

mod commitment;
pub mod witness;

pub use commitment::{Commitment, SignedCommitment};

use codec::{Codec, Decode, Encode};
use sp_core::H256;
use sp_std::prelude::*;

/// Key type for BEEFY module.
pub const KEY_TYPE: sp_application_crypto::KeyTypeId = sp_application_crypto::KeyTypeId(*b"beef");

/// BEEFY application-specific crypto types using ECDSA.
pub mod ecdsa {
	mod app_ecdsa {
		use sp_application_crypto::{app_crypto, ecdsa};
		app_crypto!(ecdsa, crate::KEY_TYPE);
	}

	sp_application_crypto::with_pair! {
		/// A BEEFY authority keypair using ECDSA as its crypto.
		pub type AuthorityPair = app_ecdsa::Pair;
	}

	/// Identity of a BEEFY authority using ECDSA as its crypto.
	pub type AuthorityId = app_ecdsa::Public;

	/// Signature for a BEEFY authority using ECDSA as its crypto.
	pub type AuthoritySignature = app_ecdsa::Signature;
}

/// The `ConsensusEngineId` of BEEFY.
pub const BEEFY_ENGINE_ID: sp_runtime::ConsensusEngineId = *b"BEEF";

/// A typedef for validator set id.
pub type ValidatorSetId = u64;

/// The index of an authority.
pub type AuthorityIndex = u32;

/// The type used to represent an MMR root hash.
pub type MmrRootHash = H256;

/// A consensus log item for BEEFY.
#[derive(Decode, Encode)]
pub enum ConsensusLog<AuthorityId: Codec> {
	/// The authorities have changed.
	#[codec(index = 1)]
	AuthoritiesChange {
		/// Set of new validators to be used
		new_validator_set: Vec<AuthorityId>,
		/// Id for this new set of validators
		new_validator_set_id: ValidatorSetId,
	},
	/// Disable the authority with given index.
	#[codec(index = 2)]
	OnDisabled(AuthorityIndex),
	/// MMR root hash.
	#[codec(index = 3)]
	MmrRoot(MmrRootHash),
}

sp_api::decl_runtime_apis! {
	/// API necessary for BEEFY voters.
	pub trait BeefyApi<AuthorityId: Codec> {
		/// Return the current set of authorities.
		fn authorities() -> Vec<AuthorityId>;
	}
}
