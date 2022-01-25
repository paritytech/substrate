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

//! Key related CLI utilities

use super::{
	generate::GenerateCmd, generate_node_key::GenerateNodeKeyCmd, insert_key::InsertKeyCmd,
	inspect_key::InspectKeyCmd, inspect_node_key::InspectNodeKeyCmd,
};
use crate::{Error, SubstrateCli};

/// Key utilities for the cli.
#[derive(Debug, clap::Subcommand)]
pub enum KeySubcommand {
	/// Generate a random node libp2p key, save it to file or print it to stdout
	/// and print its peer ID to stderr.
	GenerateNodeKey(GenerateNodeKeyCmd),

	/// Generate a random account
	Generate(GenerateCmd),

	/// Gets a public key and a SS58 address from the provided Secret URI
	Inspect(InspectKeyCmd),

	/// Print the peer ID corresponding to the node key in the given file
	InspectNodeKey(InspectNodeKeyCmd),

	/// Insert a key to the keystore of a node.
	Insert(InsertKeyCmd),
}

impl KeySubcommand {
	/// run the key subcommands
	pub fn run<C: SubstrateCli>(&self, cli: &C) -> Result<(), Error> {
		match self {
			KeySubcommand::GenerateNodeKey(cmd) => cmd.run(),
			KeySubcommand::Generate(cmd) => cmd.run(),
			KeySubcommand::Inspect(cmd) => cmd.run(),
			KeySubcommand::Insert(cmd) => cmd.run(cli),
			KeySubcommand::InspectNodeKey(cmd) => cmd.run(),
		}
	}
}
