use sc_cli_derive::substrate_cli_params;

struct MyCommand {
	shared: sc_cli::SharedParams,
}

#[substrate_cli_params(
	shared_params = shared,
	unknown_attr = 42,
)]
impl sc_cli::CliConfiguration for MyCommand {
	fn is_dev(&self) -> sc_cli::Result<bool> {
		// override: this function will be used preferably over the value in SharedParams
		Ok(true)
	}
}

fn main() {}
