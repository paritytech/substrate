// Copyright 2020-2021 Parity Technologies (UK) Ltd.
// This file is part of Cumulus.

// Cumulus is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Cumulus is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Cumulus.  If not, see <http://www.gnu.org/licenses/>.

#![allow(missing_docs)]

use cumulus_test_runtime::{AccountId, Signature};
use sc_chain_spec::{ChainSpecExtension, ChainSpecGroup};
use sc_service::ChainType;
use serde::{Deserialize, Serialize};
use sp_core::{sr25519, Pair, Public};
use sp_runtime::traits::{IdentifyAccount, Verify};

/// Specialized `ChainSpec` for the normal parachain runtime.
pub type ChainSpec = sc_service::GenericChainSpec<GenesisExt, Extensions>;

/// Extension for the genesis config to add custom keys easily.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct GenesisExt {
	/// The runtime genesis config.
	runtime_genesis_config: cumulus_test_runtime::GenesisConfig,
}

impl sp_runtime::BuildStorage for GenesisExt {
	fn assimilate_storage(&self, storage: &mut sp_core::storage::Storage) -> Result<(), String> {
		sp_state_machine::BasicExternalities::execute_with_storage(storage, || {
			sp_io::storage::set(cumulus_test_runtime::TEST_RUNTIME_UPGRADE_KEY, &vec![1, 2, 3, 4]);
		});

		self.runtime_genesis_config.assimilate_storage(storage)
	}
}

/// Helper function to generate a crypto pair from seed
pub fn get_from_seed<TPublic: Public>(seed: &str) -> <TPublic::Pair as Pair>::Public {
	TPublic::Pair::from_string(&format!("//{}", seed), None)
		.expect("static values are valid; qed")
		.public()
}


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, ChainSpecGroup)]
#[serde(deny_unknown_fields)]
pub struct Extension1 {
	pub test: u64,
}

	
/// The extensions for the [`ChainSpec`].
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, ChainSpecGroup, ChainSpecExtension)]
#[serde(deny_unknown_fields)]
pub struct Extensions {
	ext1: Extension1
}

impl Extensions {
	/// Try to get the extension from the given `ChainSpec`.
	pub fn try_get(chain_spec: &dyn sc_service::ChainSpec) -> Option<&Self> {
		sc_chain_spec::get_extension(chain_spec.extensions())
	}
}

type AccountPublic = <Signature as Verify>::Signer;

/// Helper function to generate an account ID from seed.
pub fn get_account_id_from_seed<TPublic: Public>(seed: &str) -> AccountId
where
	AccountPublic: From<<TPublic::Pair as Pair>::Public>,
{
	AccountPublic::from(get_from_seed::<TPublic>(seed)).into_account()
}

/// Get the chain spec for a specific parachain ID.
pub fn get_chain_spec() -> ChainSpec {
	ChainSpec::from_genesis(
		"Local Testnet",
		"local_testnet",
		ChainType::Local,
		move || GenesisExt { runtime_genesis_config: local_testnet_genesis() },
		Vec::new(),
		None,
		None,
		None,
		Extensions {ext1: Extension1{test:0} },
	)
}

/// Local testnet genesis for testing.
pub fn local_testnet_genesis() -> cumulus_test_runtime::GenesisConfig {
	testnet_genesis(
		get_account_id_from_seed::<sr25519::Public>("Alice"),
		vec![
			get_account_id_from_seed::<sr25519::Public>("Alice"),
			get_account_id_from_seed::<sr25519::Public>("Bob"),
			get_account_id_from_seed::<sr25519::Public>("Charlie"),
			get_account_id_from_seed::<sr25519::Public>("Dave"),
			get_account_id_from_seed::<sr25519::Public>("Eve"),
			get_account_id_from_seed::<sr25519::Public>("Ferdie"),
			get_account_id_from_seed::<sr25519::Public>("Alice//stash"),
			get_account_id_from_seed::<sr25519::Public>("Bob//stash"),
			get_account_id_from_seed::<sr25519::Public>("Charlie//stash"),
			get_account_id_from_seed::<sr25519::Public>("Dave//stash"),
			get_account_id_from_seed::<sr25519::Public>("Eve//stash"),
			get_account_id_from_seed::<sr25519::Public>("Ferdie//stash"),
		],
	)
}

fn testnet_genesis(
	root_key: AccountId,
	endowed_accounts: Vec<AccountId>,
) -> cumulus_test_runtime::GenesisConfig {
	cumulus_test_runtime::GenesisConfig::default()
	// cumulus_test_runtime::GenesisConfig {
	// 	system: cumulus_test_runtime::SystemConfig {
	// 		code: cumulus_test_runtime::WASM_BINARY
	// 			.expect("WASM binary was not build, please build it!")
	// 			.to_vec(),
	// 		..Default::default()
	// 	},
	// 	// parachain_system: Default::default(),
	// 	balances: cumulus_test_runtime::BalancesConfig {
	// 		balances: endowed_accounts.iter().cloned().map(|k| (k, 1 << 60)).collect(),
	// 	},
	// 	sudo: cumulus_test_runtime::SudoConfig { key: root_key },
	// }
}
