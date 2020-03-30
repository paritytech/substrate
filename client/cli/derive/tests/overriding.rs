use sc_cli::{CliConfiguration, Result, SharedParams, SubstrateCli};
use sc_cli_derive::{substrate_cli, substrate_cli_config_wrapper, substrate_cli_params};

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

#[derive(Clone)]
struct MyCommand {
	shared: SharedParams,
}

#[substrate_cli_params(
	shared_params = shared,
)]
impl CliConfiguration for MyCommand {
	fn chain_id(&self, _is_dev: bool) -> Result<String> {
		Ok("It works!".to_string())
	}
}

#[test]
fn substrate_cli_params() {
	let cmd = MyCommand {
		shared: SharedParams {
			base_path: None,
			chain: None,
			dev: false,
			log: None,
		},
	};

	assert_eq!(cmd.chain_id(true).ok(), Some("It works!".to_string()));
}

struct Wrapper {
	inner: MyCommand,
}

#[substrate_cli_config_wrapper(inner)]
impl CliConfiguration for Wrapper {
	fn is_dev(&self) -> Result<bool> {
		Ok(true)
	}
}

#[test]
fn substrate_cli_config_wrapper() {
	let wrapped = MyCommand {
		shared: SharedParams {
			base_path: None,
			chain: None,
			dev: false,
			log: None,
		},
	};

	let wrapper = Wrapper {
		inner: wrapped.clone(),
	};

	assert_eq!(wrapped.is_dev().ok(), Some(false));
	assert_eq!(wrapper.is_dev().ok(), Some(true));
}
