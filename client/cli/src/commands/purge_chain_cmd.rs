use std::fmt::Debug;
use std::io::{Write, self};
use std::fs;
use structopt::StructOpt;
use sc_service::{
	Configuration, ChainSpecExtension, RuntimeGenesis,
	config::{DatabaseConfig},
};

use crate::error;
use crate::params::SharedParams;

/// The `purge-chain` command used to remove the whole chain.
#[derive(Debug, StructOpt, Clone)]
pub struct PurgeChainCmd {
	/// Skip interactive prompt by answering yes automatically.
	#[structopt(short = "y")]
	pub yes: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl PurgeChainCmd {
	/// Run the purge command
	pub fn run<G, E>(
		self,
		mut config: Configuration<G, E>,
	) -> error::Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		assert!(config.chain_spec.is_some(), "chain_spec must be present before continuing");

		config.use_in_memory_keystore()?;

		let db_path = match config.expect_database() {
			DatabaseConfig::Path { path, .. } => path,
			_ => {
				eprintln!("Cannot purge custom database implementation");
				return Ok(());
			}
		};

		if !self.yes {
			print!("Are you sure to remove {:?}? [y/N]: ", &db_path);
			io::stdout().flush().expect("failed to flush stdout");

			let mut input = String::new();
			io::stdin().read_line(&mut input)?;
			let input = input.trim();

			match input.chars().nth(0) {
				Some('y') | Some('Y') => {},
				_ => {
					println!("Aborted");
					return Ok(());
				},
			}
		}

		match fs::remove_dir_all(&db_path) {
			Ok(_) => {
				println!("{:?} removed.", &db_path);
				Ok(())
			},
			Err(ref err) if err.kind() == io::ErrorKind::NotFound => {
				eprintln!("{:?} did not exist.", &db_path);
				Ok(())
			},
			Err(err) => Result::Err(err.into())
		}
	}
}
