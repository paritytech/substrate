use crate::service;
use futures::{future::{select, Map}, FutureExt, TryFutureExt, channel::oneshot, compat::Future01CompatExt};
use std::cell::RefCell;
use tokio::runtime::Runtime;
pub use sc_cli::{VersionInfo, IntoExit, error};
use sc_cli::{display_role, informant, parse_and_prepare, ParseAndPrepare, NoCustom, CoreParams};
use sc_service::{AbstractService, Roles as ServiceRoles, Configuration};
use sp_consensus_aura::sr25519::{AuthorityPair as AuraPair};
use crate::chain_spec;
use log::info;

/// Parse command line arguments into service configuration.
pub fn run<I, T, E>(args: I, version: VersionInfo) -> error::Result<()> where
	I: IntoIterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
	E: IntoExit,
{
	let opt = CoreParams::from_iter(args);
	todo!();
	/*
	type Config<T> = Configuration<(), T>;

	Ok(())
	*/
}

fn load_spec(id: &str) -> Result<Option<chain_spec::ChainSpec>, String> {
	Ok(match chain_spec::Alternative::from(id) {
		Some(spec) => Some(spec.load()?),
		None => None,
	})
}
