// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Implementation of the `insert` subcommand

use crate::{Error, KeystoreParams, CryptoSchemeFlag, SharedParams, utils, with_crypto_scheme};
use structopt::StructOpt;
use sp_core::{crypto::KeyTypeId, traits::BareCryptoStore};
use std::convert::TryFrom;
use sc_service::config::KeystoreConfig;
use sc_keystore::Store as KeyStore;
use sp_core::crypto::SecretString;

/// The `insert` command
#[derive(Debug, StructOpt)]
#[structopt(
	name = "insert",
	about = "Insert a key to the keystore of a node."
)]
pub struct InsertCmd {
	/// The secret key URI.
	/// If the value is a file, the file content is used as URI.
	/// If not given, you will be prompted for the URI.
	#[structopt(long)]
	suri: Option<String>,

	/// Key type, examples: "gran", or "imon"
	#[structopt(long)]
	key_type: String,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub keystore_params: KeystoreParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub crypto_scheme: CryptoSchemeFlag,
}

impl InsertCmd {
	/// Run the command
	pub fn run(&self) -> Result<(), Error> {
		let suri = utils::read_uri(self.suri.as_ref())?;
		let base_path = self.shared_params.base_path.as_ref()
			.ok_or_else(|| Error::Other("please supply base path".into()))?;

		let (keystore, public) = match self.keystore_params.keystore_config(base_path)? {
			KeystoreConfig::Path { path, password } => {
				let public = with_crypto_scheme!(
					self.crypto_scheme.scheme,
					to_vec(&suri, password.clone())
				)?;
				let keystore = KeyStore::open(path, password)
					.map_err(|e| format!("{}", e))?;
				(keystore, public)
			},
			_ => unreachable!("keystore_config always returns path and password; qed")
		};

		let key_type = KeyTypeId::try_from(self.key_type.as_str())
			.map_err(|_| {
				Error::Other("Cannot convert argument to keytype: argument should be 4-character string".into())
			})?;

		keystore.write()
			.insert_unknown(key_type, &suri, &public[..])
			.map_err(|e| Error::Other(format!("{:?}", e)))?;

		Ok(())
	}
}

fn to_vec<P: sp_core::Pair>(uri: &str, pass: Option<SecretString>) -> Result<Vec<u8>, Error> {
	let p = utils::pair_from_suri::<P>(uri, pass)?;
	Ok(p.public().as_ref().to_vec())
}
