use sc_cli_derive::substrate_cli_config_wrapper;

struct Wrapper {
	foo: u32,
}

#[substrate_cli_config_wrapper(bar)]
impl sc_cli::CliConfiguration for Wrapper {}

fn main() {}
