#![allow(unused_variables, dead_code)]

use sc_cli_derive::spec_factory;
use serde::{Deserialize, Serialize};
use sp_runtime::BuildStorage;
use sp_storage::Storage;

#[derive(Serialize, Deserialize)]
struct MyGenesisConfig;
struct MyExtension;
struct MyCli;

impl BuildStorage for MyGenesisConfig {
	fn assimilate_storage(&self, _: &mut Storage) -> Result<(), String> {
		unimplemented!()
	}
}

#[spec_factory(cli = MyCli, support_url = "http://example.org", copyright_start_year = 2020)]
fn spec_factory(id: &str) -> Result<Option<sc_service::ChainSpec<MyGenesisConfig>>, String> {
	Ok(None)
}

fn main() {}
