use sc_cli::{CliConfiguration, Result, SharedParams, SubstrateCli};
use sc_cli_derive::substrate_cli;

struct MyCli {}

#[substrate_cli(
	support_url = "http://example.org",
	copyright_start_year = 2020,
	impl_version = "0.1.0",
)]
impl SubstrateCli for MyCli {
	fn load_spec(&self, _id: &str) -> std::result::Result<Box<dyn sc_service::ChainSpec>, String> {
		unimplemented!()
	}

	fn impl_name() -> &'static str {
		"It works!"
	}
}

#[test]
fn substrate_cli() {
	assert_eq!(MyCli::impl_name(), "It works!");
}
