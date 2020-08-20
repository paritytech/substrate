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

use crate::Error;
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

#[cfg(test)]
mod tests {
	use super::*;
	use tempfile::Builder;
	use std::io::Read;

	#[test]
	fn generate_node_key() {
		let mut file = Builder::new().prefix("keyfile").tempfile().unwrap();
		let generate =
			GenerateNodeKeyCmd::from_iter(&["generate-node-key", "--file", "/tmp/keyfile"]);
		assert!(generate.run().is_ok());
		let mut buf = String::new();
		assert!(file.read_to_string(&mut buf).is_ok());
		assert!(hex::decode(buf).is_ok());
	}
}
