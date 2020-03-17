use sc_cli_derive::spec_factory;

mod sc_service {
	pub struct ChainSpec<G, E = ()>;
	pub trait SubstrateCli<G, E = ()> {
		fn load_spec(id: &str) -> Result<Option<ChainSpec<G, E>>, String>;
		fn get_impl_name() -> &'static str;
		fn get_impl_version() -> &'static str;
	}
}

struct MyGenesisConfig;
struct MyExtension;
struct MyCli;

#[spec_factory(cli = MyCli)]
fn load_spec(id: &str) -> Result<Option<sc_service::ChainSpec<MyGenesisConfig>>, String> {
	Ok(None)
}

fn main() {
}
