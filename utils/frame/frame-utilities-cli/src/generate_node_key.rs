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

//! Implementation of the `generate-node-key` subcommand

use sc_cli::{Error, SharedParams, CliConfiguration};
use structopt::StructOpt;
use std::{path::PathBuf, fs};
use libp2p::identity::{ed25519 as libp2p_ed25519, PublicKey};

/// The `generate-node-key` command
#[derive(Debug, StructOpt)]
#[structopt(
	name = "generate-node-key",
	about = "Generate a random node libp2p key, save it to file and print its peer ID"
)]
pub struct GenerateNodeKeyCmd {
	/// Name of file to save secret key to.
	#[structopt(long)]
	file: PathBuf,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl GenerateNodeKeyCmd {
	/// Run the command
	pub fn run(&self) -> Result<(), Error> {
		let file = &self.file;

		let keypair = libp2p_ed25519::Keypair::generate();
		let secret = keypair.secret();
		let peer_id = PublicKey::Ed25519(keypair.public()).into_peer_id();

		fs::write(file, hex::encode(secret.as_ref()))?;

		println!("{}", peer_id);

		Ok(())
	}
}

impl CliConfiguration for GenerateNodeKeyCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn inspect_node_key() {
		let path = tempfile::tempdir().unwrap().into_path().join("node-id").into_os_string();
		let path = path.to_str().unwrap();
		let cmd = GenerateNodeKeyCmd::from_iter(&["generate-node-key", "--file", path.clone()]);

		assert!(cmd.run().is_ok());
	}
}
