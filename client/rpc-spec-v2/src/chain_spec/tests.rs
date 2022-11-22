// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use super::*;
use jsonrpsee::{types::EmptyParams, RpcModule};
use sc_chain_spec::Properties;

const CHAIN_NAME: &'static str = "TEST_CHAIN_NAME";
const CHAIN_GENESIS: [u8; 32] = [0; 32];
const CHAIN_PROPERTIES: &'static str = r#"{"three": "123", "one": 1, "two": 12}"#;

fn api() -> RpcModule<ChainSpec> {
	ChainSpec::new(
		CHAIN_NAME.to_string(),
		CHAIN_GENESIS,
		serde_json::from_str(CHAIN_PROPERTIES).unwrap(),
	)
	.into_rpc()
}

#[tokio::test]
async fn chain_spec_chain_name_works() {
	let name = api()
		.call::<_, String>("chainSpec_unstable_chainName", EmptyParams::new())
		.await
		.unwrap();
	assert_eq!(name, CHAIN_NAME);
}

#[tokio::test]
async fn chain_spec_genesis_hash_works() {
	let genesis = api()
		.call::<_, String>("chainSpec_unstable_genesisHash", EmptyParams::new())
		.await
		.unwrap();
	assert_eq!(genesis, format!("0x{}", hex::encode(CHAIN_GENESIS)));
}

#[tokio::test]
async fn chain_spec_properties_works() {
	let properties = api()
		.call::<_, Properties>("chainSpec_unstable_properties", EmptyParams::new())
		.await
		.unwrap();
	assert_eq!(properties, serde_json::from_str(CHAIN_PROPERTIES).unwrap());
}
