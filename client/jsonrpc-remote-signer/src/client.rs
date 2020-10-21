// This file is part of Substrate.

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

/// Client implementation of SSRS using hyper

use async_trait::async_trait;
use tokio::sync::RwLock;
use std::sync::Arc;
use sp_core::{
	crypto::{CryptoTypePublicPair, KeyTypeId },
	sr25519::{Public as Sr25519Public},
};
use sp_keystore::{
	CryptoStore, Error as CryptoStoreError, SyncCryptoStore,
	SyncCryptoStorePtr,
	vrf::{VRFTranscriptData, VRFSignature},
};
use sp_application_crypto::{ed25519, sr25519, ecdsa};

use futures::compat::Future01CompatExt;
use url::Url;

use crate::gen_client::Client;
use jsonrpc_client_transports::transports::{http, ws};

/// A remote based keystore that is either memory-based or filesystem-based.
pub struct RemoteKeystore {
	client: RwLock<Option<Client>>,
	url: Url,
	max_retry: u8,
}

impl RemoteKeystore {
	/// Create a local keystore from filesystem.
	pub fn open(url: String, max_retry: Option<u8>) -> Result<Self, String> {
		let url : Url = url
			.parse()
			.map_err(|e| format!("Parsing Remote Signer URL failed: {:?}", e))?;

		match url.scheme() {
			"http" | "https" | "ws" | "wss" => {},
			_ => return Err(format!("Remote Signer doesn't speak {:}", url.scheme()))
		};

		Ok(RemoteKeystore{
			client: RwLock::new(None),
			url,
			max_retry: max_retry.unwrap_or(10),
		})
	}

	/// Create a local keystore in memory.
	async fn ensure_connected(&self) -> Result<(), CryptoStoreError> {
		let mut w = self.client.write().await;
		if w.is_some() {
			return Ok(())
		}

		log::info!{
			target: "remote_keystore" ,
			"Connecting to {:}", self.url
		};

		let mut counter = 0;
		loop {
			let client = match self.url.scheme() {
				"http" | "https" => {
					let (sender, receiver) = futures::channel::oneshot::channel();
					let url = self.url.clone().into_string();
					std::thread::spawn(move || {
						let connect = hyper::rt::lazy(move || {
							use jsonrpc_core::futures::Future;
							http::connect(&url)
								.then(|client| {
									if sender.send(client).is_err() {
										panic!("The caller did not wait for the server.");
									}
									// TODO kill the tokio runtime now and the thread in case
									// `client.is_err()`
									Ok(())
								})
						});
						hyper::rt::run(connect);
					});

					receiver.await.expect("Always sends something")
				},
				"ws" | "wss" => {
					ws::connect::<Client>(&self.url).compat().await
				},
				_ => unreachable!()
			};

			match client {
				Ok(client) => {
					*w = Some(client);
					return Ok(());
				},
				Err(e) => {
					log::warn!{
						target: "remote_keystore",
						"Attempt {} failed: {}", counter, e
					}
				}
			}

			counter += 1;
			if self.max_retry > 0 && counter >= self.max_retry {
				log::error!{
					target: "remote_keystore",
					"Retrying to connect {:} failed {} times. Quitting.", self.url, counter
				}
				return Err(CryptoStoreError::Unavailable)
			}
		}


	}
}

#[async_trait]
impl CryptoStore for RemoteKeystore {
	async fn keys(
		&self,
		id: KeyTypeId
	) -> std::result::Result<Vec<CryptoTypePublicPair>, CryptoStoreError> {
		self.ensure_connected().await?;
		let client = self.client.read().await;
		client
			.as_ref()
			.ok_or(CryptoStoreError::Unavailable)?
			.keys(id)
			.compat()
			.await
			.map_err(|e|CryptoStoreError::Other(format!("{:}", e)) )
	}

	async fn supported_keys(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>
	) -> std::result::Result<Vec<CryptoTypePublicPair>, CryptoStoreError> {
		self.ensure_connected().await?;
		let client = self.client.read().await;
		client
			.as_ref()
			.ok_or(CryptoStoreError::Unavailable)?
			.supported_keys(id, keys)
			.compat()
			.await
			.map_err(|e|CryptoStoreError::Other(format!("{:}", e)) )
	}

	async fn sign_with(
		&self,
		id: KeyTypeId,
		key: &CryptoTypePublicPair,
		msg: &[u8],
	) -> std::result::Result<Vec<u8>, CryptoStoreError> {
		self.ensure_connected().await?;
		let client = self.client.read().await;
		client
			.as_ref()
			.ok_or(CryptoStoreError::Unavailable)?
			.sign_with(id, key.clone(), msg.to_vec())
			.compat()
			.await
			.map_err(|e|CryptoStoreError::Other(format!("{:}", e)) )
	}

	async fn sr25519_public_keys(&self, key_type: KeyTypeId) -> Vec<sr25519::Public> {
		if self.ensure_connected().await.is_err() {
			return vec![]
		};

		let client = self.client.read().await;
		match client.as_ref() {
			Some(c) => c
				.sr25519_public_keys(key_type)
				.compat()
				.await
				.unwrap_or(vec![]),
			_ => unreachable!()
		}
	}

	async fn sr25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<sr25519::Public, CryptoStoreError> {
		self.ensure_connected().await?;

		let client = self.client.read().await;
		client
			.as_ref()
			.ok_or(CryptoStoreError::Unavailable)?
			.sr25519_generate_new(id, seed.map(|s| s.to_string()))
			.compat()
			.await
			.map_err(|e|CryptoStoreError::Other(format!("{:}", e)) )
	}

	async fn ed25519_public_keys(&self, key_type: KeyTypeId) -> Vec<ed25519::Public> {
		if self.ensure_connected().await.is_err() {
			return vec![]
		};

		let client = self.client.read().await;
		match client.as_ref() {
			Some(c) => c
				.ed25519_public_keys(key_type)
				.compat()
				.await
				.unwrap_or(vec![]),
			_ => unreachable!()
		}
	}

	async fn ed25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<ed25519::Public, CryptoStoreError> {
		self.ensure_connected().await?;

		let client = self.client.read().await;
		client
			.as_ref()
			.ok_or(CryptoStoreError::Unavailable)?
			.ed25519_generate_new(id, seed.map(|s| s.to_string()))
			.compat()
			.await
			.map_err(|e|CryptoStoreError::Other(format!("{:}", e)) )
	}

	async fn ecdsa_public_keys(&self, key_type: KeyTypeId) -> Vec<ecdsa::Public> {
		if self.ensure_connected().await.is_err() {
			return vec![]
		};

		let client = self.client.read().await;
		match client.as_ref() {
			Some(c) => c
				.ecdsa_public_keys(key_type)
				.compat()
				.await
				.unwrap_or(vec![]),
			_ => unreachable!()
		}

	}

	async fn ecdsa_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<ecdsa::Public, CryptoStoreError> {
		self.ensure_connected().await?;

		let client = self.client.read().await;
		client
			.as_ref()
			.ok_or(CryptoStoreError::Unavailable)?
			.ecdsa_generate_new(id, seed.map(|s| s.to_string()))
			.compat()
			.await
			.map_err(|e|CryptoStoreError::Other(format!("{:}", e)) )
	}

	async fn insert_unknown(&self, key_type: KeyTypeId, suri: &str, public: &[u8])
		-> std::result::Result<(), ()>
	{
		self.ensure_connected().await.map_err(|_|())?;

		let client = self.client.read().await;
		client
			.as_ref()
			.ok_or(())?
			.insert_unknown(key_type, suri.to_string(), public.to_vec())
			.compat()
			.await
			.map_err(|_| () )
	}

	async fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool {
		if self.ensure_connected().await.is_err() {
			return false
		};

		let client = self.client.read().await;
		match client.as_ref() {
			Some(c) => c
				.has_keys(public_keys.to_vec())
				.compat()
				.await
				.unwrap_or(false),
			_ => false
		}
	}

	async fn sr25519_vrf_sign(
		&self,
		key_type: KeyTypeId,
		public: &Sr25519Public,
		transcript_data: VRFTranscriptData,
	) -> std::result::Result<VRFSignature, CryptoStoreError> {

		self.ensure_connected().await?;
		let client = self.client.read().await;
		client
			.as_ref()
			.ok_or(CryptoStoreError::Unavailable)?
			.sr25519_vrf_sign(key_type, public.clone(), transcript_data.into())
			.compat()
			.await
			.map_err(|e|CryptoStoreError::Other(format!("{:}", e)) )
	}
}

impl SyncCryptoStore for RemoteKeystore {
	fn keys(
		&self,
		id: KeyTypeId
	) -> std::result::Result<Vec<CryptoTypePublicPair>, CryptoStoreError> {
		futures::executor::block_on(CryptoStore::keys(self, id))
	}

	fn supported_keys(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>
	) -> std::result::Result<Vec<CryptoTypePublicPair>, CryptoStoreError> {
		futures::executor::block_on(CryptoStore::supported_keys(self, id, keys))
	}

	fn sign_with(
		&self,
		id: KeyTypeId,
		key: &CryptoTypePublicPair,
		msg: &[u8],
	) -> std::result::Result<Vec<u8>, CryptoStoreError> {
		futures::executor::block_on(CryptoStore::sign_with(self, id, key, msg))
	}

	fn sr25519_public_keys(&self, key_type: KeyTypeId) -> Vec<sr25519::Public> {
		futures::executor::block_on(CryptoStore::sr25519_public_keys(self, key_type))
	}

	fn sr25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<sr25519::Public, CryptoStoreError> {
		futures::executor::block_on(CryptoStore::sr25519_generate_new(self, id, seed))
	}

	fn ed25519_public_keys(&self, key_type: KeyTypeId) -> Vec<ed25519::Public> {
		futures::executor::block_on(CryptoStore::ed25519_public_keys(self, key_type))
	}

	fn ed25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<ed25519::Public, CryptoStoreError> {
		futures::executor::block_on(CryptoStore::ed25519_generate_new(self, id, seed))
	}

	fn ecdsa_public_keys(&self, key_type: KeyTypeId) -> Vec<ecdsa::Public> {
		futures::executor::block_on(CryptoStore::ecdsa_public_keys(self, key_type))
	}

	fn ecdsa_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<ecdsa::Public, CryptoStoreError> {
		futures::executor::block_on(CryptoStore::ecdsa_generate_new(self, id, seed))
	}

	fn insert_unknown(&self, key_type: KeyTypeId, suri: &str, public: &[u8])
		-> std::result::Result<(), ()>
	{
		futures::executor::block_on(CryptoStore::insert_unknown(self, key_type, suri, public))
	}

	fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool {
		futures::executor::block_on(CryptoStore::has_keys(self, public_keys))
	}

	fn sr25519_vrf_sign(
		&self,
		key_type: KeyTypeId,
		public: &Sr25519Public,
		transcript_data: VRFTranscriptData,
	) -> std::result::Result<VRFSignature, CryptoStoreError> {
		futures::executor::block_on(CryptoStore::sr25519_vrf_sign(
			self, key_type, public, transcript_data))
	}
}

impl Into<SyncCryptoStorePtr> for RemoteKeystore {
	fn into(self) -> SyncCryptoStorePtr {
		Arc::new(self)
	}
}

impl Into<Arc<dyn CryptoStore>> for RemoteKeystore {
	fn into(self) -> Arc<dyn CryptoStore> {
		Arc::new(self)
	}
}
