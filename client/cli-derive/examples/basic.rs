use sc_cli_derive::spec_factory;

mod sc_service {
	pub struct ChainSpec<G, E = ()>;
}

mod sc_cli {
	pub trait SubstrateCLI<G, E = ()> {
		fn load_spec(id: &str) -> Result<Option<ChainSpec<G, E>>, String>;
		fn get_impl_name() -> &'static str;
		fn get_impl_version() -> &'static str;
		fn get_support_url() -> &'static str;
		fn get_executable_name() -> &'static str;
		fn get_author() -> &'static str;
		fn get_description() -> &'static str;
		fn get_copyright_start_year() -> i32;
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
