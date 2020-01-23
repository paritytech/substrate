use crate::service;
pub use sc_cli::{VersionInfo, error};
use sc_cli::CoreParams;
use sp_consensus_aura::sr25519::{AuthorityPair as AuraPair};
use crate::chain_spec;

/// Parse command line arguments into service configuration.
pub fn run<I, T>(args: I, version: VersionInfo) -> error::Result<()>
where
	I: Iterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
{
	let args: Vec<_> = args.collect();
	let core_params = sc_cli::from_iter::<CoreParams, _>(args.clone(), &version);

	let mut config = sc_service::Configuration::default();
	config.impl_name = "node-template";

	sc_cli::run(
		config,
		core_params,
		service::new_light,
		service::new_full,
		load_spec,
		|config: _| Ok(new_full_start!(config).0),
		&version,
	)
}

fn load_spec(id: &str) -> Result<Option<chain_spec::ChainSpec>, String> {
	Ok(match chain_spec::Alternative::from(id) {
		Some(spec) => Some(spec.load()?),
		None => None,
	})
}
