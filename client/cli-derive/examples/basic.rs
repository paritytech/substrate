use sc_cli_derive::spec_factory;
//use sc_service::{ChainSpec, RuntimeGenesis};

struct ChainSpec<G, E = ()>;
struct GenesisConfig;
struct Extension;

#[spec_factory]
fn load_spec(id: &str) -> Result<Option<ChainSpec<GenesisConfig>>, String> {
	Ok(None)
}

fn main() {
}
