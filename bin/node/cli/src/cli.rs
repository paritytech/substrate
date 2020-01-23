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

pub use sc_cli::VersionInfo;
use sc_cli::{SharedParams, ImportParams, error};
use sc_service::{Roles as ServiceRoles, Configuration};
use structopt::StructOpt;
use sc_cli::{CoreParams, RunCmd};
use crate::{service, ChainSpec, load_spec};
use crate::factory_impl::FactoryState;
use node_transaction_factory::RuntimeAdapter;

#[derive(Clone, Debug, StructOpt)]
#[structopt(settings = &[
	structopt::clap::AppSettings::GlobalVersion,
	structopt::clap::AppSettings::ArgsNegateSubcommands,
	structopt::clap::AppSettings::SubcommandsNegateReqs,
])]
enum Cli {
	#[structopt(flatten)]
	SubstrateCli(CoreParams),
	/// The custom factory subcommmand for manufacturing transactions.
	#[structopt(
		name = "factory",
		about = "Manufactures num transactions from Alice to random accounts. \
		Only supported for development or local testnet."
	)]
	Factory(FactoryCmd),
}

/// The `factory` command used to generate transactions.
/// Please note: this command currently only works on an empty database!
#[derive(Debug, StructOpt, Clone)]
pub struct FactoryCmd {
	/// How often to repeat. This option only has an effect in mode `MasterToNToM`.
	#[structopt(long="rounds", default_value = "1")]
	pub rounds: u64,

	/// MasterToN: Manufacture `num` transactions from the master account
	///            to `num` randomly created accounts, one each.
	///
	/// MasterTo1: Manufacture `num` transactions from the master account
	///            to exactly one other randomly created account.
	///
	/// MasterToNToM: Manufacture `num` transactions from the master account
	///               to `num` randomly created accounts.
	///               From each of these randomly created accounts manufacture
	///               a transaction to another randomly created account.
	///               Repeat this `rounds` times. If `rounds` = 1 the behavior
	///               is the same as `MasterToN`.{n}
	///               A -> B, A -> C, A -> D, ... x `num`{n}
	///               B -> E, C -> F, D -> G, ...{n}
	///               ... x `rounds`
	///
	/// These three modes control manufacturing.
	#[structopt(long="mode", default_value = "MasterToN")]
	pub mode: node_transaction_factory::Mode,

	/// Number of transactions to generate. In mode `MasterNToNToM` this is
	/// the number of transactions per round.
	#[structopt(long="num", default_value = "8")]
	pub num: u64,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub import_params: ImportParams,
}

/// Parse command line arguments into service configuration.
pub fn run<I, T>(args: I, version: sc_cli::VersionInfo) -> error::Result<()>
where
	I: Iterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
{
	type Config<A, B> = Configuration<A, B>;

	let args: Vec<_> = args.collect();
	let subcommand = match sc_cli::try_from_iter::<RunCmd, _>(args.clone(), &version) {
		Ok(opt) => Cli::SubstrateCli(CoreParams::Run(opt)),
		Err(_) => sc_cli::from_iter::<Cli, _>(args.clone(), &version),
	};

	let mut config = sc_service::Configuration::default();
	config.impl_name = "substrate-node";

	match subcommand {
		Cli::SubstrateCli(cli) => sc_cli::run(
			config,
			cli,
			service::new_light,
			service::new_full,
			load_spec,
			|config: Config<_, _>| Ok(new_full_start!(config).0),
			&version,
		),
		Cli::Factory(cli_args) => {
			sc_cli::init(&mut config, load_spec, &cli_args.shared_params, &version)?;

			sc_cli::fill_import_params(
				&mut config,
				&cli_args.import_params,
				ServiceRoles::FULL,
				cli_args.shared_params.dev,
			)?;

			match ChainSpec::from(config.expect_chain_spec().id()) {
				Some(ref c) if c == &ChainSpec::Development || c == &ChainSpec::LocalTestnet => {},
				_ => panic!("Factory is only supported for development and local testnet."),
			}

			let factory_state = FactoryState::new(
				cli_args.mode.clone(),
				cli_args.num,
				cli_args.rounds,
			);

			let service_builder = new_full_start!(config).0;
			node_transaction_factory::factory::<FactoryState<_>, _, _, _, _, _>(
				factory_state,
				service_builder.client(),
				service_builder.select_chain()
					.expect("The select_chain is always initialized by new_full_start!; QED")
			).map_err(|e| format!("Error in transaction factory: {}", e))?;

			Ok(())
		},
	}
}
