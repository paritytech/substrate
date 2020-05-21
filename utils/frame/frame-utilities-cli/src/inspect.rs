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

//! Implementation of the `inspect` subcommand

use sc_cli::{
	print_from_uri, CliConfiguration, KeystoreParams, SharedParams, read_uri,
	with_crypto_scheme, NetworkSchemeFlag, OutputTypeFlag, CryptoSchemeFlag, Error,
};
use structopt::StructOpt;

/// The `inspect` command
#[derive(Debug, StructOpt, Clone)]
#[structopt(
	name = "inspect-key",
	about = "Gets a public key and a SS58 address from the provided Secret URI"
)]
pub struct InspectCmd {
	/// A Key URI to be inspected. May be a secret seed, secret URI
	/// (with derivation paths and password), SS58 or public URI.
	/// If the value is a file, the file content is used as URI.
	/// If not given, you will be prompted for the URI.
	#[structopt(long)]
	uri: Option<String>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub keystore_params: KeystoreParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub network_scheme: NetworkSchemeFlag,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub output_scheme: OutputTypeFlag,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub crypto_scheme: CryptoSchemeFlag,
}

impl InspectCmd {
	/// Run the command
	pub fn run(&self) -> Result<(), Error> {
		let uri = read_uri(self.uri.as_ref())?;
		let pass = self.keystore_params.read_password().ok();

		with_crypto_scheme!(
			self.crypto_scheme.scheme,
			print_from_uri(
				&uri,
				pass.as_ref().map(String::as_str),
				self.network_scheme.network.clone(),
				self.output_scheme.output_type.clone()
			)
		);

		Ok(())
	}
}

impl CliConfiguration for InspectCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn keystore_params(&self) -> Option<&KeystoreParams> {
		Some(&self.keystore_params)
	}
}
