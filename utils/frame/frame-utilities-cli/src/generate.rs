// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

//! Implementation of the `generate` subcommand
use bip39::{MnemonicType, Mnemonic, Language};
use structopt::StructOpt;
use sc_cli::{
	print_from_uri, CliConfiguration, KeystoreParams, SharedParams, Error,
	with_crypto_scheme, NetworkSchemeFlag, OutputTypeFlag, CryptoSchemeFlag,
};

/// The `generate` command
#[derive(Debug, StructOpt, Clone)]
#[structopt(name = "generate", about = "Generate a random account")]
pub struct GenerateCmd {
	/// The number of words in the phrase to generate. One of 12 default), 15, 18, 21 and 24.
	#[structopt(long, short = "w", value_name = "WORDS")]
	words: Option<usize>,

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

impl GenerateCmd {
	/// Run the command
	pub fn run(&self) -> Result<(), Error> {
		let words = match self.words {
			Some(words) => {
				MnemonicType::for_word_count(words)
					.map_err(|_| {
						Error::Input("Invalid number of words given for phrase: must be 12/15/18/21/24".into())
					})?
			},
			None => MnemonicType::Words12,
		};
		let mnemonic = Mnemonic::new(words, Language::English);
		let password = self.keystore_params.read_password()?;
		let maybe_network = self.network_scheme.network.clone();
		let output = self.output_scheme.output_type.clone();

		with_crypto_scheme!(
			self.crypto_scheme.scheme,
			print_from_uri(
				mnemonic.phrase(),
				Some(password.as_str()),
				maybe_network,
				output
			)
		);
		Ok(())
	}
}

impl CliConfiguration for GenerateCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn keystore_params(&self) -> Option<&KeystoreParams> {
		Some(&self.keystore_params)
	}
}
