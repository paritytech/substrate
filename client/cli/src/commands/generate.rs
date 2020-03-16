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

use super::{SharedParams, RuntimeAdapter, get_password};
use crate::error::{self, Error};
use bip39::{MnemonicType, Mnemonic, Language};
use structopt::StructOpt;
use crate::{AccountIdFor, VersionInfo};
use sp_core::crypto::{Ss58Codec, Derive};
use sc_service::{Configuration, ChainSpec};

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
	pub fn run<RA: RuntimeAdapter>(self) -> error::Result<()>
		where
			AccountIdFor<RA>: Ss58Codec + Derive,
	{
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
		let password = get_password(&self.shared_params)?;
		let maybe_network = self.shared_params.network;
		let output = self.shared_params.output_type;

		RA::print_from_uri(
			mnemonic.phrase(),
			Some(password.as_str()),
			maybe_network,
			output
		);

		Ok(())
	}

	/// Update and prepare a `Configuration` with command line parameters
	pub fn update_config<F>(
		&self,
		mut config: &mut Configuration,
		spec_factory: F,
		version: &VersionInfo,
	) -> error::Result<()> where
		F: FnOnce(&str) -> Result<Box<dyn ChainSpec>, String>,
	{
		self.shared_params.update_config(&mut config, spec_factory, version)?;
		config.use_in_memory_keystore()?;

		Ok(())
	}
}
