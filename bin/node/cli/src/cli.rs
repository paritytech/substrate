// Copyright 2018-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

pub use sc_cli::{VersionInfo, DEFAULT_KEYSTORE_CONFIG_PATH};
use tokio::runtime::{Builder as RuntimeBuilder, Runtime};
use sc_cli::{IntoExit, NoCustom, SharedParams, ImportParams, error};
use sc_service::{AbstractService, Roles as ServiceRoles, Configuration, config::KeystoreConfig};
use log::info;
use structopt::StructOpt;
use sc_cli::{display_role, parse_and_prepare, GetSharedParams, ParseAndPrepare};
use crate::{service, ChainSpec, load_spec};
use crate::factory_impl::RuntimeState;
use node_transaction_factory::FactoryState;
use node_transaction_factory::automata::Automaton;
use node_transaction_factory::{RuntimeAdapter, Options as FactoryOptions};
use futures::{channel::oneshot, future::{select, Either}};

/// Custom subcommands.
#[derive(Clone, Debug, StructOpt)]
pub enum CustomSubcommands {
	/// The custom benchmark subcommmand for manufacturing transactions.
	#[structopt(
		name = "benchmark",
		about = "Benchmark transactions. \
		Only supported for development or local testnet."
	)]
	Factory(FactoryCmd),
}

impl GetSharedParams for CustomSubcommands {
	fn shared_params(&self) -> Option<&SharedParams> {
		match self {
			CustomSubcommands::Factory(cmd) => Some(&cmd.shared_params),
		}
	}
}

/// The `factory` command used to generate transactions.
/// Please note: this command currently only works on an empty database!
#[derive(Debug, StructOpt, Clone)]
pub struct FactoryCmd {
	/// Path to bench file.
	#[structopt(long="bench-file", default_value = "./factory_tests/test.txt")]
	pub bench_file: String,

	/// Number of blocks to generate.
	#[structopt(long="blocks", default_value = "10")]
	pub blocks: u32,

	/// Number of transactions to generate per block.
	#[structopt(long="tx-per-block", default_value = "10")]
	pub tx_per_block: u32,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub import_params: ImportParams,
}

/// Parse command line arguments into service configuration.
pub fn run<I, T, E>(args: I, exit: E, version: sc_cli::VersionInfo) -> error::Result<()> where
	I: IntoIterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
	E: IntoExit,
{
	type Config<A, B> = Configuration<(), A, B>;

	match parse_and_prepare::<CustomSubcommands, NoCustom, _>(&version, "substrate-node", args) {
		ParseAndPrepare::Run(cmd) => cmd.run(load_spec, exit,
		|exit, _cli_args, _custom_args, config: Config<_, _>| {
			info!("{}", version.name);
			info!("  version {}", config.full_version());
			info!("  by Parity Technologies, 2017-2019");
			info!("Chain specification: {}", config.chain_spec.name());
			info!("Node name: {}", config.name);
			info!("Roles: {}", display_role(&config));
			let runtime = RuntimeBuilder::new()
				.thread_name("main-tokio-")
				.threaded_scheduler()
				.build()
				.map_err(|e| format!("{:?}", e))?;
			match config.roles {
				ServiceRoles::LIGHT => run_until_exit(
					runtime,
					service::new_light(config)?,
					exit
				),
				_ => run_until_exit(
					runtime,
					service::new_full(config)?,
					exit
				),
			}
		}),
		ParseAndPrepare::BuildSpec(cmd) => cmd.run::<NoCustom, _, _, _>(load_spec),
		ParseAndPrepare::ExportBlocks(cmd) => cmd.run_with_builder(|config: Config<_, _>|
			Ok(new_full_start!(config).0), load_spec, exit),
		ParseAndPrepare::ImportBlocks(cmd) => cmd.run_with_builder(|config: Config<_, _>|
			Ok(new_full_start!(config).0), load_spec, exit),
		ParseAndPrepare::CheckBlock(cmd) => cmd.run_with_builder(|config: Config<_, _>|
			Ok(new_full_start!(config).0), load_spec, exit),
		ParseAndPrepare::PurgeChain(cmd) => cmd.run(load_spec),
		ParseAndPrepare::RevertChain(cmd) => cmd.run_with_builder(|config: Config<_, _>|
			Ok(new_full_start!(config).0), load_spec),
		ParseAndPrepare::CustomCommand(CustomSubcommands::Factory(cli_args)) => {
			let mut config: Config<_, _> = sc_cli::create_config_with_db_path(
				load_spec,
				&cli_args.shared_params,
				&version,
				None,
			)?;
			sc_cli::fill_import_params(&mut config, &cli_args.import_params, ServiceRoles::FULL)?;

			config.keystore = KeystoreConfig::Path {
				path: config.in_chain_config_dir(DEFAULT_KEYSTORE_CONFIG_PATH).unwrap(),
				password: None,
			};
			
			// Tracing
			config.tracing_targets = cli_args.shared_params.tracing_targets.into();
			config.tracing_receiver = cli_args.shared_params.tracing_receiver.into();
			if let Some(tracing_targets) = config.tracing_targets.as_ref() {
				let subscriber = sc_tracing::ProfilingSubscriber::new(
					config.tracing_receiver.clone(),
					tracing_targets,
				);
				match tracing::subscriber::set_global_default(subscriber) {
					Ok(_) => (),
					Err(e) => panic!("Unable to set global default subscriber {}", e),
				}
			}

			match ChainSpec::from(config.chain_spec.id()) {
				Some(ref c) if c == &ChainSpec::Development || c == &ChainSpec::LocalTestnet => {},
				_ => panic!("Factory is only supported for development and local testnet."),
			}

			let automaton = Automaton::new_from_file(String::from("./factory_tests/test.txt"));
			let runtime_state = RuntimeState::new();

			let options = FactoryOptions {
				bench_file: cli_args.bench_file,
				blocks: cli_args.blocks,
				tx_per_block: cli_args.tx_per_block,
			};
			let service_builder = new_full_start!(config).0;
			let mut factory_state = FactoryState::new(
				service_builder.client().clone(),
				service_builder.select_chain().expect("initialized by new_full_start").clone(),
				automaton,
				runtime_state,
				options,
			);
			factory_state.run().map_err(|e| format!("Error in transaction factory: {}", e))?;

			Ok(())
		}
	}
}

fn run_until_exit<T, E>(
	mut runtime: Runtime,
	service: T,
	e: E,
) -> error::Result<()>
where
	T: AbstractService,
	E: IntoExit,
{
	let (exit_send, exit) = oneshot::channel();

	let informant = sc_cli::informant::build(&service);

	let handle = runtime.spawn(select(exit, informant));

	// we eagerly drop the service so that the internal exit future is fired,
	// but we need to keep holding a reference to the global telemetry guard
	let _telemetry = service.telemetry();

	let exit = e.into_exit();
	let service_res = runtime.block_on(select(service, exit));

	let _ = exit_send.send(());

	runtime.block_on(handle);

	match service_res {
		Either::Left((res, _)) => res.map_err(error::Error::Service),
		Either::Right((_, _)) => Ok(())
	}
}
