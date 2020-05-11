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

//! Implementation of the `generate-node-key` subcommand

use crate::{error, SharedParams, CliConfiguration};
use structopt::StructOpt;
use std::{path::PathBuf, fs};
use libp2p::identity::{ed25519 as libp2p_ed25519, PublicKey};

/// The `generate-node-id` command
#[derive(Debug, StructOpt, Clone)]
#[structopt(
	name = "generate-node-id",
	about = "Generate a random node libp2p key, save it to file and print its peer ID"
)]
pub struct GenerateNodeIdCmd {
	/// Name of file to save secret key to.
	#[structopt(long)]
	file: PathBuf,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl GenerateNodeIdCmd {
	/// Run the command
	pub fn run(&self) -> error::Result<()> {
		let file = &self.file;

		let keypair = libp2p_ed25519::Keypair::generate();
		let secret = keypair.secret();
		let peer_id = PublicKey::Ed25519(keypair.public()).into_peer_id();

		fs::write(file, hex::encode(secret.as_ref()))?;

		println!("{}", peer_id);

		Ok(())
	}
}

impl CliConfiguration for GenerateNodeIdCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}
}
