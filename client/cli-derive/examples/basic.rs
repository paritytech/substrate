#![allow(unused_variables, dead_code)]

use sc_cli::{CliConfiguration, ImportParams, KeystoreParams, SharedParams, SubstrateCLI};
use sc_cli_derive::{load_spec, substrate_cli_params};

struct MyCli {
	shared: SharedParams,
	import: ImportParams,
	keystore: KeystoreParams,
}

#[load_spec(
	support_url = "http://example.org",
	copyright_start_year = 2020,
	impl_version = "0.1.0",
)]
impl SubstrateCLI for MyCli {
	fn load_spec(&self, id: &str) -> Result<Box<dyn sc_service::ChainSpec>, String> {
		Err("not implemented".into())
	}
}

#[substrate_cli_params(shared_params = shared, import_params = import, keystore_params = keystore)]
impl CliConfiguration for MyCli {}

fn main() {}
