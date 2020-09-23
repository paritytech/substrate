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

use crate::{
	utils, KeystoreParams, with_crypto_scheme, NetworkSchemeFlag,
	OutputTypeFlag, CryptoSchemeFlag, Error,
};
use structopt::StructOpt;
/// The `inspect` command
#[derive(Debug, StructOpt)]
#[structopt(
	name = "inspect-key",
	about = "Gets a public key and a SS58 address from the provided Secret URI"
)]
pub struct InspectKeyCmd {
	/// A Key URI to be inspected. May be a secret seed, secret URI
	/// (with derivation paths and password), SS58 or public URI.
	///
	/// If the given value is a file, the file content will be used
	/// as URI.
	///
	/// If omitted, you will be prompted for the URI.
	uri: Option<String>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub keystore_params: KeystoreParams,

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

impl InspectKeyCmd {
	/// Run the command
	pub fn run(&self) -> Result<(), Error> {
		let uri = utils::read_uri(self.uri.as_ref())?;
		let password = self.keystore_params.read_password()?;

		use utils::print_from_uri;
		with_crypto_scheme!(
			self.crypto_scheme.scheme,
			print_from_uri(
				&uri,
				password,
				self.network_scheme.network.clone(),
				self.output_scheme.output_type.clone()
			)
		);

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use structopt::StructOpt;

	#[test]
	fn inspect() {
		let words =
			"remember fiber forum demise paper uniform squirrel feel access exclude casual effort";
		let seed = "0xad1fb77243b536b90cfe5f0d351ab1b1ac40e3890b41dc64f766ee56340cfca5";

		let inspect =
			InspectKeyCmd::from_iter(&["inspect-key", words, "--password", "12345"]);
		assert!(inspect.run().is_ok());

		let inspect = InspectKeyCmd::from_iter(&["inspect-key", seed]);
		assert!(inspect.run().is_ok());
	}
}
