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

//! frame-system CLI utilities

mod generate;
mod generate_node_key;
mod insert;
mod inspect;
mod inspect_node_key;
mod module_id;
mod key;
mod utils;
mod sign_transaction;
#[cfg(feature = "balances")]
mod transfer;
#[cfg(feature = "balances")]
pub use transfer::TransferCmd;

pub use {
	key::KeySubcommand,
	module_id::ModuleIdCmd,
	generate::GenerateCmd,
	insert::InsertCmd,
	inspect::InspectCmd,
	inspect_node_key::InspectNodeKeyCmd,
	sign_transaction::SignTransactionCmd,
	generate_node_key::GenerateNodeKeyCmd,
};


#[cfg(test)]
mod tests {
	use super::{generate::GenerateCmd, generate_node_key::GenerateNodeKeyCmd, inspect::InspectCmd};
	use tempfile::Builder;
	use structopt::StructOpt;
	use std::io::Read;

	#[test]
	fn generate() {
		let generate = GenerateCmd::from_iter(&["generate", "--password", "12345"]);
		assert!(generate.run().is_ok())
	}

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

	#[test]
	fn inspect() {
		let words =
			"remember fiber forum demise paper uniform squirrel feel access exclude casual effort";
		let seed = "0xad1fb77243b536b90cfe5f0d351ab1b1ac40e3890b41dc64f766ee56340cfca5";

		let inspect =
			InspectCmd::from_iter(&["inspect-key", "--uri", words, "--password", "12345"]);
		assert!(inspect.run().is_ok());

		let inspect = InspectCmd::from_iter(&["inspect-key", "--uri", seed]);
		assert!(inspect.run().is_ok());
	}
}
