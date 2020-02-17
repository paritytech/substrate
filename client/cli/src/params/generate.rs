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

use super::{SharedParams, RunCmd, Crypto, get_password};
use crate::error::{self, Error};
use bip39::{Language, Mnemonic, MnemonicType};
use structopt::StructOpt;

/// The `generate` command
#[derive(Debug, StructOpt, Clone)]
#[structopt(name = "generate", about = "Generate a random account")]
pub struct GenerateCmd {
	/// The number of words in the phrase to generate. One of 12 default), 15, 18, 21 and 24.
	#[structopt(long, short = "w", value_name = "WORDS")]
	words: Option<usize>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl GenerateCmd {
	/// Run the command
	pub fn run<C: Crypto>(
		self,
		run_cmd: RunCmd,
	) -> error::Result<()> {
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
		let password = get_password(&run_cmd)?;
		let maybe_network = self.shared_params.network;
		let output = self.shared_params.output_type;

		C::print_from_uri(
			mnemonic.phrase(),
			password.as_ref().map(String::as_str),
			maybe_network,
			output
		);

		Ok(())
	}
}
