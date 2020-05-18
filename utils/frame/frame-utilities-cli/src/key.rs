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

//! Key related CLI utilities

use sc_cli::{Error, substrate_cli_subcommands};
use structopt::StructOpt;
use cli_utils::{HashFor, RuntimeAdapter};
use serde::{de::DeserializeOwned, Serialize};

use crate::{
	generate_node_key::GenerateNodeIdCmd,
	generate::GenerateCmd,
	inspect::InspectCmd,
	insert::InsertCmd
};

/// key utilities for the cli.
#[derive(Debug, Clone, StructOpt)]
pub enum KeySubcommand {
	/// Generate a random node libp2p key, save it to file and print its peer ID
	GenerateNodeKey(GenerateNodeIdCmd),

	/// Generate a random account
	Generate(GenerateCmd),

	/// Gets a public key and a SS58 address from the provided Secret URI
	InspectKey(InspectCmd),

	/// Insert a key to the keystore of a node.
	Insert(InsertCmd),
}

impl KeySubcommand {
	/// run the key subcommands
	pub fn run<RA>(&self) -> Result<(), Error>
		where
			RA: RuntimeAdapter,
			HashFor<RA>: DeserializeOwned + Serialize + Send + Sync,
	{
		match self {
			KeySubcommand::GenerateNodeKey(cmd) => cmd.run(),
			KeySubcommand::Generate(cmd) => cmd.run(),
			KeySubcommand::InspectKey(cmd) => cmd.run(),
			KeySubcommand::Insert(cmd) => cmd.run::<RA>(),
		}
	}
}

// CliConfiguration implementation
substrate_cli_subcommands!(
	KeySubcommand =>
	GenerateNodeKey,
	Generate,
	InspectKey,
	Insert
);
