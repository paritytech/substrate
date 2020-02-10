use std::fmt::Debug;
use std::io::{Read, Write, Seek, self};
use std::fs;
use std::{str::FromStr, path::PathBuf};
use structopt::{StructOpt, clap::arg_enum};
use log::info;
use sc_network::{
	config::{build_multiaddr, NonReservedPeerMode, TransportConfig, NodeKeyConfig},
	multiaddr::Protocol,
};
use sc_service::{
	AbstractService, Configuration, ChainSpecExtension, RuntimeGenesis, ServiceBuilderCommand,
	config::{DatabaseConfig, KeystoreConfig}, ChainSpec, PruningMode,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use crate::error;
use crate::params::BlockNumber;
use crate::runtime::run_until_exit;
use crate::execution_strategy::*;
use crate::execution_strategy::ExecutionStrategy;
use crate::commands::shared_params::SharedParams;
use crate::commands::node_key_params::NodeKeyParams;
use crate::commands::import_params::ImportParams;

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
