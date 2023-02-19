// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Implementation of the `generate` subcommand
use crate::{
	utils::print_from_uri, with_crypto_scheme, CryptoSchemeFlag, Error, KeystoreParams,
	NetworkSchemeFlag, OutputTypeFlag,
};
use bip39::{Language, Mnemonic, MnemonicType};
use clap::Parser;

/// The `generate` command
#[derive(Debug, Clone, Parser)]
#[command(name = "generate", about = "Generate a random account")]
pub struct GenerateCmd {
	/// The number of words in the phrase to generate. One of 12 (default), 15, 18, 21 and 24.
	#[arg(short = 'w', long, value_name = "WORDS")]
	words: Option<usize>,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub keystore_params: KeystoreParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub network_scheme: NetworkSchemeFlag,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub output_scheme: OutputTypeFlag,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub crypto_scheme: CryptoSchemeFlag,
}

impl GenerateCmd {
	/// Run the command
	pub fn run(&self) -> Result<(), Error> {
		let words = match self.words {
			Some(words) => MnemonicType::for_word_count(words).map_err(|_| {
				Error::Input(
					"Invalid number of words given for phrase: must be 12/15/18/21/24".into(),
				)
			})?,
			None => MnemonicType::Words12,
		};
		let mnemonic = Mnemonic::new(words, Language::English);
		let password = self.keystore_params.read_password()?;
		let output = self.output_scheme.output_type;

		with_crypto_scheme!(
			self.crypto_scheme.scheme,
			print_from_uri(mnemonic.phrase(), password, self.network_scheme.network, output)
		);
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn generate() {
		let generate = GenerateCmd::parse_from(&["generate", "--password", "12345"]);
		assert!(generate.run().is_ok())
	}
}
