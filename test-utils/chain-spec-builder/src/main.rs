use clap::{App, load_yaml};

use node_cli::chain_spec;
use substrate_service::chain_ops::build_spec;

fn genesis_constructor() -> chain_spec::GenesisConfig {
	let yaml = load_yaml!("./cli.yml");
	let matches = App::from_yaml(yaml).get_matches();
	let authorities = matches.values_of("initial_authority_seed")
		.unwrap()
		.map(chain_spec::get_authority_keys_from_seed)
		.collect();

	let endowed_accounts = matches.values_of("endowed_account_seed")
		.unwrap()
		.map(chain_spec::get_account_id_from_seed)
		.collect();

	let sudo_key_seed = matches.value_of("sudo_key_seed").unwrap();
	let sudo_key = chain_spec::get_account_id_from_seed(sudo_key_seed);

	let enable_println = true;

	chain_spec::testnet_genesis(
		authorities,
		sudo_key.into(),
		Some(endowed_accounts),
		enable_println,
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
		None,
	);
	build_spec(chain_spec, false).unwrap()
}

fn main() {
	let json = generate_chain_spec();
	println!("{}", json);
}
