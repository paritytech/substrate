// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Substrate CLI library.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

extern crate tokio;

extern crate substrate_cli as cli;
extern crate node_service as service;
extern crate exit_future;

#[macro_use]
extern crate log;

pub use cli::error;

use tokio::runtime::Runtime;
pub use service::{Components as ServiceComponents, Service, CustomConfiguration, ServiceFactory};
pub use cli::{VersionInfo, IntoExit};

/// The chain specification option.
#[derive(Clone, Debug)]
pub enum ChainSpec {
	/// Whatever the current runtime is, with just Alice as an auth.
	Development,
	/// Whatever the current runtime is, with simple Alice/Bob auths.
	LocalTestnet,
	/// The BBQ Birch testnet.
	BbqBirch,
	/// Whatever the current runtime is with the "global testnet" defaults.
	StagingTestnet,
}

/// Get a chain config from a spec setting.
impl ChainSpec {
	pub(crate) fn load(self) -> Result<service::ChainSpec, String> {
		Ok(match self {
			ChainSpec::BbqBirch => service::chain_spec::bbq_birch_config()?,
			ChainSpec::Development => service::chain_spec::development_config(),
			ChainSpec::LocalTestnet => service::chain_spec::local_testnet_config(),
			ChainSpec::StagingTestnet => service::chain_spec::staging_testnet_config(),
		})
	}

	pub(crate) fn from(s: &str) -> Option<Self> {
		match s {
			"dev" => Some(ChainSpec::Development),
			"local" => Some(ChainSpec::LocalTestnet),
			"" | "bbq-birch" => Some(ChainSpec::BbqBirch),
			"staging" => Some(ChainSpec::StagingTestnet),
			_ => None,
		}
	}
}

fn load_spec(id: &str) -> Result<Option<service::ChainSpec>, String> {
	Ok(match ChainSpec::from(id) {
		Some(spec) => Some(spec.load()?),
		None => None,
	})
}

/// Parse command line arguments into service configuration.
pub fn run<I, T, E>(args: I, exit: E, version: cli::VersionInfo) -> error::Result<()> where
	I: IntoIterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
	E: IntoExit,
{
	match cli::prepare_execution::<service::Factory, _, _, _, _>(args, exit, version, load_spec, "substrate-node")? {
		cli::Action::ExecutedInternally => (),
		cli::Action::RunService((config, exit)) => {
			info!("Substrate Node");
			info!("  version {}", config.full_version());
			info!("  by Parity Technologies, 2017, 2018");
			info!("Chain specification: {}", config.chain_spec.name());
			info!("Node name: {}", config.name);
			info!("Roles: {:?}", config.roles);
			let mut runtime = Runtime::new()?;
			let executor = runtime.executor();
			match config.roles == service::Roles::LIGHT {
				true => run_until_exit(&mut runtime, service::Factory::new_light(config, executor)?, exit)?,
				false => run_until_exit(&mut runtime, service::Factory::new_full(config, executor)?, exit)?,
			}
		}
	}
	Ok(())
}

fn run_until_exit<C, E>(
	runtime: &mut Runtime,
	service: service::Service<C>,
	e: E,
) -> error::Result<()>
	where
		C: service::Components,
		E: IntoExit,
{
	let (exit_send, exit) = exit_future::signal();

	let executor = runtime.executor();
	cli::informant::start(&service, exit.clone(), executor.clone());

	let _ = runtime.block_on(e.into_exit());
	exit_send.fire();
	Ok(())
}
