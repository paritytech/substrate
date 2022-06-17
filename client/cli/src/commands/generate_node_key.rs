// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
use clap::Parser;
use libp2p::identity::{ed25519 as libp2p_ed25519, PublicKey};
use std::{
	fs,
	io::{self, Write},
	path::PathBuf,
};

/// The `generate-node-key` command
#[derive(Debug, Parser)]
#[clap(
	name = "generate-node-key",
	about = "Generate a random node key, write it to a file or stdout \
		 	and write the corresponding peer-id to stderr"
)]
pub struct GenerateNodeKeyCmd {
	/// Name of file to save secret key to.
	///
	/// If not given, the secret key is printed to stdout.
	#[clap(long)]
	file: Option<PathBuf>,

	/// The output is in raw binary format.
	///
	/// If not given, the output is written as an hex encoded string.
	#[clap(long)]
	bin: bool,
}

impl GenerateNodeKeyCmd {
	/// Run the command
	pub fn run(&self) -> Result<(), Error> {
		let keypair = libp2p_ed25519::Keypair::generate();

		let secret = keypair.secret();

		let file_data = if self.bin {
			secret.as_ref().to_owned()
		} else {
			hex::encode(secret.as_ref()).into_bytes()
		};

		match &self.file {
			Some(file) => fs::write(file, file_data)?,
			None => io::stdout().lock().write_all(&file_data)?,
		}

		eprintln!("{}", PublicKey::Ed25519(keypair.public()).to_peer_id());

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::io::Read;
	use tempfile::Builder;

	#[test]
	fn generate_node_key() {
		let mut file = Builder::new().prefix("keyfile").tempfile().unwrap();
		let file_path = file.path().display().to_string();
		let generate = GenerateNodeKeyCmd::parse_from(&["generate-node-key", "--file", &file_path]);
		assert!(generate.run().is_ok());
		let mut buf = String::new();
		assert!(file.read_to_string(&mut buf).is_ok());
		assert!(hex::decode(buf).is_ok());
	}
}
