#[macro_use]
extern crate clap;

use clap::App;

extern crate node_cli;
extern crate substrate_service;
extern crate substrate_primitives;

use node_cli::chain_spec::{ChainSpec, GenesisConfig, get_authority_id_from_seed, testnet_genesis};
use substrate_service::chain_ops::build_spec;

fn genesis_constructor() -> GenesisConfig {
    let yaml = load_yaml!("./cli.yml");
    let matches = App::from_yaml(yaml).get_matches();
    let authorities = matches.values_of("initial_authority_seed")
        .unwrap()
        .map(get_authority_id_from_seed)
        .collect();

    let endowed_accounts = matches.values_of("endowed_account_seed")
        .unwrap()
        .map(get_authority_id_from_seed)
        .collect();

    let upgrade_key_seed = matches.value_of("upgrade_key_seed").unwrap();
    let upgrade_key = get_authority_id_from_seed(upgrade_key_seed);
    testnet_genesis(
        authorities,
        upgrade_key.into(),
        Some(endowed_accounts),
    )
}

fn generate_chain_spec()-> String {
    let chain_spec = ChainSpec::from_genesis(
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
