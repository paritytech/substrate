// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use crate::{Error, NetworkSchemeFlag};
use std::fs;
use libp2p::identity::{PublicKey, ed25519};
use std::path::PathBuf;
use structopt::StructOpt;

/// The `inspect-node-key` command
#[derive(Debug, StructOpt)]
#[structopt(
	name = "inspect-node-key",
	about = "Print the peer ID corresponding to the node key in the given file."
)]
pub struct InspectNodeKeyCmd {
	/// Name of file to read the secret key from.
	#[structopt(long)]
	file: PathBuf,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub network_scheme: NetworkSchemeFlag,
}

impl InspectNodeKeyCmd {
	/// runs the command
	pub fn run(&self) -> Result<(), Error> {
		let mut file_content = hex::decode(fs::read(&self.file)?)
			.map_err(|_| "failed to decode secret as hex")?;
		let secret = ed25519::SecretKey::from_bytes(&mut file_content)
			.map_err(|_| "Bad node key file")?;

		let keypair = ed25519::Keypair::from(secret);
		let peer_id = PublicKey::Ed25519(keypair.public()).into_peer_id();

		println!("{}", peer_id);

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::super::GenerateNodeKeyCmd;

	#[test]
	fn inspect_node_key() {
		let path = tempfile::tempdir().unwrap().into_path().join("node-id").into_os_string();
		let path = path.to_str().unwrap();
		let cmd = GenerateNodeKeyCmd::from_iter(&["generate-node-key", "--file", path.clone()]);

		assert!(cmd.run().is_ok());

		let cmd = InspectNodeKeyCmd::from_iter(&["inspect-node-key", "--file", path]);
		assert!(cmd.run().is_ok());
	}
}
