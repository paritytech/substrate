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

use crate::error;
use super::{SharedParams, RunCmd, get_password, read_uri, Crypto};
use structopt::StructOpt;
use std::{path::PathBuf, fs};
use libp2p::identity::{ed25519 as libp2p_ed25519, PublicKey};

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
	pub fn run<C: Crypto>(self, run_cmd: RunCmd) -> error::Result<()> {
		let uri = read_uri(self.uri)?;

		let pass = get_password(&run_cmd)?;

		C::print_from_uri(
			&uri,
			password.as_ref().map(String::as_str),
			self.shared_params.network,
			self.shared_params.output_type
		);

		Ok(())
	}
}

