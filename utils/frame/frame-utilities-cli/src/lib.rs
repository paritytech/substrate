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

//! frame-system CLI utilities

mod generate;
mod generate_node_key;
mod insert;
mod inspect;
mod key;
mod sign_transaction;

pub use {key::KeySubcommand, sign_transaction::SignTransactionCmd};

#[cfg(test)]
mod tests {
	use super::{generate::GenerateCmd, generate_node_key::GenerateNodeIdCmd, inspect::InspectCmd};
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
            GenerateNodeIdCmd::from_iter(&["generate-node-key", "--file", "/tmp/keyfile"]);
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
