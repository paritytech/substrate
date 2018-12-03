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
extern crate substrate_primitives as primitives;
extern crate node_runtime;
extern crate exit_future;
#[macro_use]
extern crate hex_literal;
#[cfg(test)]
extern crate substrate_service_test as service_test;
extern crate substrate_transaction_pool as transaction_pool;
#[macro_use]
extern crate substrate_network as network;
extern crate substrate_consensus_aura as consensus;
extern crate substrate_consensus_common as consensus_common;
extern crate substrate_client as client;
extern crate substrate_finality_grandpa as grandpa;
extern crate node_primitives;
#[macro_use]
extern crate substrate_service;
extern crate node_executor;
extern crate substrate_keystore;

#[macro_use]
extern crate log;
extern crate structopt;
extern crate parking_lot;

pub use cli::error;
pub mod chain_spec;
mod service;
mod params;

use tokio::runtime::Runtime;
pub use cli::{VersionInfo, IntoExit};
use substrate_service::{ServiceFactory, Roles as ServiceRoles};
use params::{Params as NodeParams};
use structopt::StructOpt;
use std::ops::Deref;

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
	pub(crate) fn load(self) -> Result<chain_spec::ChainSpec, String> {
		Ok(match self {
			ChainSpec::BbqBirch => chain_spec::bbq_birch_config()?,
			ChainSpec::Development => chain_spec::development_config(),
			ChainSpec::LocalTestnet => chain_spec::local_testnet_config(),
			ChainSpec::StagingTestnet => chain_spec::staging_testnet_config(),
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

fn load_spec(id: &str) -> Result<Option<chain_spec::ChainSpec>, String> {
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
	let full_version = substrate_service::config::full_version_from_strs(
		version.version,
		version.commit
	);

	let matches = match NodeParams::clap()
		.name(version.executable_name)
		.author(version.author)
		.about(version.description)
		.version(&(full_version + "\n")[..])
		.get_matches_from_safe(args) {
			Ok(m) => m,
			Err(e) => e.exit(),
		};

	let (spec, mut config) = cli::parse_matches::<service::Factory, _>(
		load_spec, version, "substrate-node", &matches
	)?;

	if matches.is_present("grandpa_authority_only") {
		config.custom.grandpa_authority = true;
		config.custom.grandpa_authority_only = true;
		// Authority Setup is only called if validator is set as true
		config.roles = ServiceRoles::AUTHORITY;
	} else if matches.is_present("grandpa_authority") {
		config.custom.grandpa_authority = true;
		// Authority Setup is only called if validator is set as true
		config.roles = ServiceRoles::AUTHORITY;
	}

	match cli::execute_default::<service::Factory, _>(spec, exit, &matches, &config)? {
		cli::Action::ExecutedInternally => (),
		cli::Action::RunService(exit) => {
			info!("Substrate Node");
			info!("  version {}", config.full_version());
			info!("  by Parity Technologies, 2017, 2018");
			info!("Chain specification: {}", config.chain_spec.name());
			info!("Node name: {}", config.name);
			info!("Roles: {:?}", config.roles);
			let mut runtime = Runtime::new()?;
			let executor = runtime.executor();
			match config.roles == ServiceRoles::LIGHT {
				true => run_until_exit(&mut runtime, service::Factory::new_light(config, executor)?, exit)?,
				false => run_until_exit(&mut runtime, service::Factory::new_full(config, executor)?, exit)?,
			}
		}
	}
	Ok(())
}

fn run_until_exit<T, C, E>(
	runtime: &mut Runtime,
	service: T,
	e: E,
) -> error::Result<()>
	where
	    T: Deref<Target=substrate_service::Service<C>>,
		C: substrate_service::Components,
		E: IntoExit,
{
	let (exit_send, exit) = exit_future::signal();

	let executor = runtime.executor();
	cli::informant::start(&service, exit.clone(), executor.clone());

	let _ = runtime.block_on(e.into_exit());
	exit_send.fire();
	Ok(())
}
