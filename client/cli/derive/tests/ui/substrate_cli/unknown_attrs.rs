use sc_cli_derive::substrate_cli;

struct MyCli {}

#[substrate_cli(
	support_url = "http://example.org",
	copyright_start_year = 2020,
	impl_version = "0.1.0",
	unknown_attrs = 42,
)]
impl sc_cli::SubstrateCli for MyCli {
	fn load_spec(&self, id: &str) -> Result<Box<dyn sc_service::ChainSpec>, String> {
		unimplemented!()
	}
}

fn main() {}
