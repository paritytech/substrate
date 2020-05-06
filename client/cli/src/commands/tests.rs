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

use super::*;
use substrate_test_runtime::Runtime;
use tempfile::Builder;
use std::io::Read;
use crate::commands::inspect::InspectCmd;
use crate::Error;

fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();
	sp_io::TestExternalities::new(t)
}

#[test]
fn generate() {
	let generate = GenerateCmd::from_iter(&["generate", "--password", "12345"]);
	assert!(generate.run().is_ok())
}

#[test]
fn generate_node_key() {
	let mut file = Builder::new()
		.prefix("keyfile")
		.tempfile()
		.unwrap();
	let generate = GenerateNodeKeyCmd::from_iter(&["generate-node-key", "--file", "/tmp/keyfile"]);
	assert!(generate.run().is_ok());
	let mut buf = String::new();
	assert!(file.read_to_string(&mut buf).is_ok());
	assert!(hex::decode(buf).is_ok());
}

#[test]
fn inspect() {
	let words = "remember fiber forum demise paper uniform squirrel feel access exclude casual effort";
	let seed = "0xad1fb77243b536b90cfe5f0d351ab1b1ac40e3890b41dc64f766ee56340cfca5";

	let inspect = InspectCmd::from_iter(&["inspect-key", "--uri", words, "--password", "12345"]);
	assert!(inspect.run().is_ok());

	let inspect = InspectCmd::from_iter(&["inspect-key", "--uri", seed]);
	assert!(inspect.run().is_ok());
}

#[test]
fn sign() {
	let words = "remember fiber forum demise paper uniform squirrel feel access exclude casual effort";
	let seed = "0xad1fb77243b536b90cfe5f0d351ab1b1ac40e3890b41dc64f766ee56340cfca5";

	let sign = SignCmd::from_iter(&["sign", "--suri", seed, "--message", &seed[2..], "--password", "12345"]);
	assert!(sign.run().is_ok());

	let sign = SignCmd::from_iter(&["sign", "--suri", words, "--message", &seed[2..]]);
	assert!(matches!(sign.run(), Err(Error::Input(_))))
}

#[test]
fn vanity() {
	let vanity = VanityCmd::from_iter(&["vanity", "--number", "1", "--pattern", "j"]);
	assert!(vanity.run().is_ok());
}

#[test]
fn transfer() {
	let seed = "0xad1fb77243b536b90cfe5f0d351ab1b1ac40e3890b41dc64f766ee56340cfca5";
	let words = "remember fiber forum demise paper uniform squirrel feel access exclude casual effort";

	let transfer = TransferCmd::from_iter(&["transfer",
		"--from", seed,
		"--to", "0xa2bc899a8a3b16a284a8cefcbc2dc48a687cd674e89b434fbbdb06f400979744",
		"--amount", "5000",
		"--index", "1",
		"--password", "12345",
	]);

	new_test_ext().execute_with(|| {
		assert!(matches!(transfer.run::<Runtime>(), Ok(())));
		let transfer = TransferCmd::from_iter(&["transfer",
			"--from", words,
			"--to", "0xa2bc899a8a3b16a284a8cefcbc2dc48a687cd674e89b434fbbdb06f400979744",
			"--amount", "5000",
			"--index", "1",
		]);
		assert!(matches!(transfer.run::<Runtime>(), Err(Error::Input(_))))
	});
}