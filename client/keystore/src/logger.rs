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

//! Keystore logging wrapper

use async_trait::async_trait;
use parking_lot::RwLock;
use sp_core::{
	crypto::{CryptoTypePublicPair, KeyTypeId, Pair as PairT, ExposeSecret, SecretString, Public},
	sr25519::{Public as Sr25519Public, Pair as Sr25519Pair},
	Encode,
};
use sp_keystore::{
	CryptoStore,
	SyncCryptoStorePtr,
	Error as TraitError,
	SyncCryptoStore,
	vrf::{VRFTranscriptData, VRFSignature, make_transcript},
};
use sp_application_crypto::{ed25519, sr25519, ecdsa, AppPair, AppKey, IsWrappedBy};
use sp_tracing::info;

use crate::{Result, Error};

/// A logging keystore that wraps any keystore and logs all access to it
pub struct TracingKeystore<C: CryptoStore>(C);

#[async_trait]
impl<C> CryptoStore for TracingKeystore<C> where C: CryptoStore {
	async fn keys(&self, id: KeyTypeId) -> std::result::Result<Vec<CryptoTypePublicPair>, TraitError> {
		sp_tracing::enter_span!(sp_tracing::Level::INFO, "keys");
		let r = self.0.keys(id).await;
		r
	}

	async fn sr25519_public_keys(&self, id: KeyTypeId) -> Vec<sr25519::Public> {
		sp_tracing::enter_span!(sp_tracing::Level::INFO, "sr25519_public_keys");
		let r = self.0.sr25519_public_keys(id).await;
		r
	}

	async fn sr25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<sr25519::Public, TraitError> {
		sp_tracing::enter_span!(sp_tracing::Level::INFO, "sr25519_generate_new");
		let r = self.0.sr25519_generate_new(id, seed).await;
		r
	}

	async fn ed25519_public_keys(&self, id: KeyTypeId) -> Vec<ed25519::Public> {
		sp_tracing::enter_span!(sp_tracing::Level::INFO, "keys");
		let r = self.0.ed25519_public_keys(id).await;
		r
	}

	async fn ed25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<ed25519::Public, TraitError> {
		sp_tracing::enter_span!(sp_tracing::Level::INFO, "ed25519_generate_new");
		let r = self.0.ed25519_generate_new(id, seed).await;
		r
	}

	async fn ecdsa_public_keys(&self, id: KeyTypeId) -> Vec<ecdsa::Public> {
		sp_tracing::enter_span!(sp_tracing::Level::INFO, "ecdsa_public_keys");
		let r = self.0.ecdsa_public_keys(id).await;
		r
	}

	async fn ecdsa_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<ecdsa::Public, TraitError> {
		sp_tracing::enter_span!(sp_tracing::Level::INFO, "ecdsa_generate_new");
		let r = self.0.ecdsa_generate_new(id, seed).await;
		r
	}

	async fn insert_unknown(&self, id: KeyTypeId, suri: &str, public: &[u8]) -> std::result::Result<(), ()> {
		sp_tracing::enter_span!(sp_tracing::Level::INFO, "insert_unknown");
		let r = self.0.insert_unknown(id, suri, public).await;
		r
	}

	async fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool {
		sp_tracing::enter_span!(sp_tracing::Level::INFO, "has_keys");
		let r = self.0.has_keys(public_keys).await;
		r
	}

	async fn supported_keys(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>,
	) -> std::result::Result<Vec<CryptoTypePublicPair>, TraitError> {

		sp_tracing::enter_span!(sp_tracing::Level::INFO, "supported_keys");
		let r = self.0.supported_keys(id, keys).await;
		r
	}

	async fn sign_with(
		&self,
		id: KeyTypeId,
		key: &CryptoTypePublicPair,
		msg: &[u8],
	) -> std::result::Result<Option<Vec<u8>>, TraitError> {

		sp_tracing::enter_span!(sp_tracing::Level::INFO, "sign_with");
		let r = self.0.sign_with(id, key, msg).await;
		r
	}

	async fn sr25519_vrf_sign(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		transcript_data: VRFTranscriptData,
	) -> std::result::Result<Option<VRFSignature>, TraitError> {

		sp_tracing::enter_span!(sp_tracing::Level::INFO, "sr25519_vrf_sign");
		let r = self.0.sr25519_vrf_sign(key_type, public, transcript_data).await;
		r
	}
}
