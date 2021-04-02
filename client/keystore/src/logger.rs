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

use parking_lot::RwLock;
use sp_application_crypto::{ecdsa, ed25519, sr25519, AppKey, AppPair, IsWrappedBy};
use sp_core::{
    crypto::{CryptoTypePublicPair, ExposeSecret, KeyTypeId, Pair as PairT, Public, SecretString},
    sr25519::{Pair as Sr25519Pair, Public as Sr25519Public},
    Encode,
};
use sp_keystore::{
    vrf::{make_transcript, VRFSignature, VRFTranscriptData},
    Error as TraitError, SyncCryptoStorePtr,
};
use sp_tracing::{debug, enter_span, info, Level};

/// A logging keystore that wraps any keystore and logs all access to it
pub struct TracingKeystore<C>(C);

impl<C> TracingKeystore<C> {
    /// Instantiate a new TracingKeystore with the given CryptoStore
    pub fn new(store: C) -> Self {
        Self(store)
    }
}

mod cryptostore {
    use super::*;
    use async_trait::async_trait;
    use sp_keystore::CryptoStore;

    #[async_trait]
    impl<C> CryptoStore for TracingKeystore<C>
    where
        C: CryptoStore,
    {
        async fn keys(&self, id: KeyTypeId) -> Result<Vec<CryptoTypePublicPair>, TraitError> {
            enter_span!(Level::INFO, "keys");
            debug!(?id, "keys params");
            let r = self.0.keys(id).await;
            debug!(result = ?r, "keys");
            r
        }

        async fn sr25519_public_keys(&self, id: KeyTypeId) -> Vec<sr25519::Public> {
            enter_span!(Level::INFO, "sr25519_public_keys");
            debug!(?id, "sr25519_public_keys params");
            let r = self.0.sr25519_public_keys(id).await;
            debug!(result = ?r, "sr25519_public_keys");
            r
        }

        async fn sr25519_generate_new(
            &self,
            id: KeyTypeId,
            seed: Option<&str>,
        ) -> Result<sr25519::Public, TraitError> {
            enter_span!(Level::INFO, "sr25519_generate_new");
            debug!(?id, ?seed, "sr25519_generate_new params");
            let r = self.0.sr25519_generate_new(id, seed).await;
            debug!(result = ?r, "sr25519_generate_new");
            r
        }

        async fn ed25519_public_keys(&self, id: KeyTypeId) -> Vec<ed25519::Public> {
            enter_span!(Level::INFO, "ed25519_public_keys");
            debug!(?id, "ed25519_public_keys params");
            let r = self.0.ed25519_public_keys(id).await;
            debug!(result = ?r, "keys");
            r
        }

        async fn ed25519_generate_new(
            &self,
            id: KeyTypeId,
            seed: Option<&str>,
        ) -> Result<ed25519::Public, TraitError> {
            enter_span!(Level::INFO, "ed25519_generate_new");
            debug!(?id, ?seed, "ed25519_generate_new params");
            let r = self.0.ed25519_generate_new(id, seed).await;
            debug!(result = ?r, "ed25519_generate_new");
            r
        }

        async fn ecdsa_public_keys(&self, id: KeyTypeId) -> Vec<ecdsa::Public> {
            enter_span!(Level::INFO, "ecdsa_public_keys");
            debug!(?id, "ecdsa_public_keys params");
            let r = self.0.ecdsa_public_keys(id).await;
            debug!(result = ?r, "ecdsa_public_keys");
            r
        }

        async fn ecdsa_generate_new(
            &self,
            id: KeyTypeId,
            seed: Option<&str>,
        ) -> Result<ecdsa::Public, TraitError> {
            enter_span!(Level::INFO, "ecdsa_generate_new");
            debug!(?id, ?seed, "ecdsa_generate_new params");
            let r = self.0.ecdsa_generate_new(id, seed).await;
            debug!(result = ?r, "ecdsa_generate_new");
            r
        }

        async fn insert_unknown(&self, id: KeyTypeId, suri: &str, public: &[u8]) -> Result<(), ()> {
            enter_span!(Level::INFO, "insert_unknown");
            debug!(?id, ?suri, ?public, "insert_unknown params");
            let r = self.0.insert_unknown(id, suri, public).await;
            debug!(result = ?r, "insert_unknown");
            r
        }

        async fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool {
            enter_span!(Level::INFO, "has_keys");
            debug!(?public_keys, "has_keys params");
            let r = self.0.has_keys(public_keys).await;
            debug!(result = ?r, "has_keys");
            r
        }

        async fn supported_keys(
            &self,
            id: KeyTypeId,
            keys: Vec<CryptoTypePublicPair>,
        ) -> Result<Vec<CryptoTypePublicPair>, TraitError> {
            enter_span!(Level::INFO, "supported_keys");
            debug!(?id, ?keys, "supported_keys params");
            let r = self.0.supported_keys(id, keys).await;
            debug!(result = ?r, "supported_keys");
            r
        }

        async fn sign_with(
            &self,
            id: KeyTypeId,
            key: &CryptoTypePublicPair,
            msg: &[u8],
        ) -> Result<Vec<u8>, TraitError> {
            enter_span!(Level::INFO, "sign_with");
            debug!(?id, ?key, ?msg, "sign_with params");
            let r = self.0.sign_with(id, key, msg).await;
            debug!(result = ?r, "sign_with");
            r
        }

        async fn sr25519_vrf_sign(
            &self,
            key_type: KeyTypeId,
            public: &sr25519::Public,
            transcript_data: VRFTranscriptData,
        ) -> Result<VRFSignature, TraitError> {
            enter_span!(Level::INFO, "sr25519_vrf_sign");
            debug!(?key_type, ?public, ?transcript_data, "sr25519_vrf_sign params");
            let r = self
                .0
                .sr25519_vrf_sign(key_type, public, transcript_data)
                .await;
            debug!(result = ?r, "sr25519_vrf_sign");
            r
        }
    }
}

mod sync_cryptostore {
    use super::*;
    use sp_keystore::SyncCryptoStore;

    impl<C> SyncCryptoStore for TracingKeystore<C>
    where
        C: SyncCryptoStore,
    {
        fn keys(&self, id: KeyTypeId) -> Result<Vec<CryptoTypePublicPair>, TraitError> {
            enter_span!(Level::INFO, "sync_keys");
            debug!(?id, "sync_keys params");
            let r = SyncCryptoStore::keys(&self.0, id);

            debug!(result = ?r, "sync_keys");
            r
        }

        fn sr25519_public_keys(&self, id: KeyTypeId) -> Vec<sr25519::Public> {
            enter_span!(Level::INFO, "sync_sr25519_public_keys");
            debug!(?id, "sync_sr25519_public_keys params");
            let r = SyncCryptoStore::sr25519_public_keys(&self.0, id);
            debug!(result = ?r, "sync_sr25519_public_keys");
            r
        }

        fn sr25519_generate_new(
            &self,
            id: KeyTypeId,
            seed: Option<&str>,
        ) -> Result<sr25519::Public, TraitError> {
            enter_span!(Level::INFO, "sync_sr25519_generate_new");
            debug!(?id, ?seed, "sync_sr25519_generate_new params");
            let r = SyncCryptoStore::sr25519_generate_new(&self.0, id, seed);
            debug!(result = ?r, "sync_sr25519_generate_new");
            r
        }

        fn ed25519_public_keys(&self, id: KeyTypeId) -> Vec<ed25519::Public> {
            enter_span!(Level::INFO, "sync_keys");
            debug!(?id, "sync_keys params");
            let r = SyncCryptoStore::ed25519_public_keys(&self.0, id);
            debug!(result = ?r, "sync_keys");
            r
        }

        fn ed25519_generate_new(
            &self,
            id: KeyTypeId,
            seed: Option<&str>,
        ) -> Result<ed25519::Public, TraitError> {
            enter_span!(Level::INFO, "sync_ed25519_generate_new");
            debug!(?id, ?seed, "sync_ed25519_generate_new params");
            let r = SyncCryptoStore::ed25519_generate_new(&self.0, id, seed);
            debug!(result = ?r, "sync_ed25519_generate_new");
            r
        }

        fn ecdsa_public_keys(&self, id: KeyTypeId) -> Vec<ecdsa::Public> {
            enter_span!(Level::INFO, "sync_ecdsa_public_keys");
            debug!(?id, "sync_ecdsa_public_keys params");
            let r = SyncCryptoStore::ecdsa_public_keys(&self.0, id);
            debug!(result = ?r, "sync_ecdsa_public_keys");
            r
        }

        fn ecdsa_generate_new(
            &self,
            id: KeyTypeId,
            seed: Option<&str>,
        ) -> Result<ecdsa::Public, TraitError> {
            enter_span!(Level::INFO, "sync_ecdsa_generate_new");
            debug!(?id, ?seed, "sync_ecdsa_generate_new params");
            let r = SyncCryptoStore::ecdsa_generate_new(&self.0, id, seed);
            debug!(result = ?r, "sync_ecdsa_generate_new");
            r
        }

        fn insert_unknown(&self, id: KeyTypeId, suri: &str, public: &[u8]) -> Result<(), ()> {
            enter_span!(Level::INFO, "sync_insert_unknown");
            debug!(?id, ?suri, ?public, "sync_insert_unknown params");
            let r = SyncCryptoStore::insert_unknown(&self.0, id, suri, public);
            debug!(result = ?r, "sync_insert_unknown");
            r
        }

        fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool {
            enter_span!(Level::INFO, "sync_has_keys");
            debug!(?public_keys, "sync_has_keys params");
            let r = SyncCryptoStore::has_keys(&self.0, public_keys);
            debug!(result = ?r, "sync_has_keys");
            r
        }

        fn supported_keys(
            &self,
            id: KeyTypeId,
            keys: Vec<CryptoTypePublicPair>,
        ) -> Result<Vec<CryptoTypePublicPair>, TraitError> {
            enter_span!(Level::INFO, "sync_supported_keys");
            debug!(?id, ?keys, "sync_supported_keys params");
            let r = SyncCryptoStore::supported_keys(&self.0, id, keys);
            debug!(result = ?r, "sync_supported_keys");
            r
        }

        fn sign_with(
            &self,
            id: KeyTypeId,
            key: &CryptoTypePublicPair,
            msg: &[u8],
        ) -> Result<Vec<u8>, TraitError> {
            enter_span!(Level::INFO, "sync_sign_with");
            debug!(?id, ?key, ?msg, "sync_sign_with params");
            let r = SyncCryptoStore::sign_with(&self.0, id, key, msg);
            debug!(result = ?r, "sync_sign_with");
            r
        }

        fn sr25519_vrf_sign(
            &self,
            key_type: KeyTypeId,
            public: &sr25519::Public,
            transcript_data: VRFTranscriptData,
        ) -> Result<VRFSignature, TraitError> {
            enter_span!(Level::INFO, "sync_sr25519_vrf_sign");
            debug!(?key_type, ?public, ?transcript_data, "sync_sr25519_vrf_sign params");
            let r = SyncCryptoStore::sr25519_vrf_sign(&self.0, key_type, public, transcript_data);
            debug!(result = ?r, "sync_sr25519_vrf_sign");
            r
        }
    }
}
