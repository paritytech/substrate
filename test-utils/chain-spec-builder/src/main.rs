#[macro_use]
extern crate clap;

use clap::App;

extern crate node_cli;
extern crate substrate_service;
extern crate substrate_primitives;

use node_cli::chain_spec;
use substrate_service::chain_ops::build_spec;

fn genesis_constructor() -> chain_spec::GenesisConfig {
	let yaml = load_yaml!("./cli.yml");
	let matches = App::from_yaml(yaml).get_matches();
	let authorities = matches.values_of("initial_authority_seed")
		.unwrap()
		.map(chain_spec::get_authority_id_from_seed)
		.collect();

	let endowed_accounts = matches.values_of("endowed_account_seed")
		.unwrap()
		.map(chain_spec::get_authority_id_from_seed)
		.collect();

	let upgrade_key_seed = matches.value_of("upgrade_key_seed").unwrap();
	let upgrade_key = chain_spec::get_authority_id_from_seed(upgrade_key_seed);
	chain_spec::testnet_genesis(
		authorities,
		upgrade_key.into(),
		Some(endowed_accounts),
	)
}

fn generate_chain_spec() -> String {
	let chain_spec = chain_spec::ChainSpec::from_genesis(
		"Custom",
		"custom",
		genesis_constructor,
		vec![],
		None,
		None,
		None,
	);
	build_spec(chain_spec, false).unwrap()
}

fn main() {
	let json = generate_chain_spec();
	println!("{}", json);
}
