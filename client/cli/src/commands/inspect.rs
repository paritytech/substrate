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

//! Implementation of the `inspect` subcommand

use crate::{error, VersionInfo, print_from_uri, with_crypto_scheme};
use super::{SharedParams, get_password, read_uri};
use structopt::StructOpt;
use sc_service::{Configuration, ChainSpec};

/// The `inspect` command
#[derive(Debug, StructOpt, Clone)]
#[structopt(
	name = "inspect",
	about = "Gets a public key and a SS58 address from the provided Secret URI"
)]
pub struct InspectCmd {
	/// A Key URI to be inspected. May be a secret seed, secret URI (with derivation paths and password), SS58 or
	/// public URI. If the value is a file, the file content is used as URI.
	/// If not given, you will be prompted for the URI.
	#[structopt(long)]
	uri: Option<String>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl InspectCmd {
	/// Run the command
	pub fn run(self) -> error::Result<()> {
		let uri = read_uri(self.uri)?;
		let pass = get_password(&self.shared_params).ok();

		with_crypto_scheme!(
			self.shared_params.scheme,
			print_from_uri(
				&uri,
				pass.as_ref().map(String::as_str),
				self.shared_params.network,
				self.shared_params.output_type
			)
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

