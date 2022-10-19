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

//! Implementation of the `inspect-node-key` subcommand

use crate::Error;
use clap::Parser;
use libp2p::identity::{ed25519, PublicKey};
use std::{
	fs,
	io::{self, Read},
	path::PathBuf,
};

/// The `inspect-node-key` command
#[derive(Debug, Parser)]
#[command(
	name = "inspect-node-key",
	about = "Load a node key from a file or stdin and print the corresponding peer-id."
)]
pub struct InspectNodeKeyCmd {
	/// Name of file to read the secret key from.
	///
	/// If not given, the secret key is read from stdin (up to EOF).
	#[arg(long)]
	file: Option<PathBuf>,

	/// The input is in raw binary format.
	///
	/// If not given, the input is read as an hex encoded string.
	#[arg(long)]
	bin: bool,

	/// This argument is deprecated and has no effect for this command.
	#[deprecated(note = "Network identifier is not used for node-key inspection")]
	#[arg(short = 'n', long = "network", value_name = "NETWORK", ignore_case = true)]
	pub network_scheme: Option<String>,
}

impl InspectNodeKeyCmd {
	/// runs the command
	pub fn run(&self) -> Result<(), Error> {
		let mut file_data = match &self.file {
			Some(file) => fs::read(&file)?,
			None => {
				let mut buf = Vec::with_capacity(64);
				io::stdin().lock().read_to_end(&mut buf)?;
				buf
			},
		};

		if !self.bin {
			// With hex input, give to the user a bit of tolerance about whitespaces
			let keyhex = String::from_utf8_lossy(&file_data);
			file_data = array_bytes::hex2bytes(keyhex.trim())
				.map_err(|_| "failed to decode secret as hex")?;
		}

		let secret =
			ed25519::SecretKey::from_bytes(&mut file_data).map_err(|_| "Bad node key file")?;

		let keypair = ed25519::Keypair::from(secret);

		println!("{}", PublicKey::Ed25519(keypair.public()).to_peer_id());

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::{super::GenerateNodeKeyCmd, *};

	#[test]
	fn inspect_node_key() {
		let path = tempfile::tempdir().unwrap().into_path().join("node-id").into_os_string();
		let path = path.to_str().unwrap();
		let cmd = GenerateNodeKeyCmd::parse_from(&["generate-node-key", "--file", path.clone()]);

		assert!(cmd.run().is_ok());

		let cmd = InspectNodeKeyCmd::parse_from(&["inspect-node-key", "--file", path]);
		assert!(cmd.run().is_ok());
	}
}
