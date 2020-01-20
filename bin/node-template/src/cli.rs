use crate::service;
pub use sc_cli::{VersionInfo, error};
use sc_cli::{CoreParams, RunCmd};
use sc_service::{AbstractService, Roles as ServiceRoles, Configuration};
use structopt::StructOpt;
use sp_consensus_aura::sr25519::{AuthorityPair as AuraPair};
use crate::chain_spec;
use log::info;

#[derive(Clone, Debug, StructOpt)]
#[structopt(settings = &[structopt::clap::AppSettings::GlobalVersion, structopt::clap::AppSettings::ArgsNegateSubcommands, structopt::clap::AppSettings::SubcommandsNegateReqs])]
struct Cli {
	#[structopt(subcommand)]
	subcommand: Option<CoreParams>,
}

/// Parse command line arguments into service configuration.
pub fn run<I, T>(args: I, version: VersionInfo) -> error::Result<()>
where
	I: Iterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
{
	type Config<A, B> = Configuration<A, B>;

	let args: Vec<_> = args.collect();
	let opt = sc_cli::from_iter::<Cli, _>(args.clone(), &version);
	let subcommand = opt.subcommand.unwrap_or_else(|| {
		let opt = sc_cli::from_iter::<RunCmd, _>(args, &version);

		eprintln!(
			"WARNING: running this command without the subcommand `run` is deprecated, please \
			use run:\n{} run [node_arguments]",
			version.executable_name,
		);
		CoreParams::Run(opt)
	});

	sc_cli::run(
		subcommand,
		service::new_light,
		service::new_full,
		load_spec,
		|config: Config<_, _>| Ok(new_full_start!(config).0),
		"substrate-node",
		&version,
	)
}

fn load_spec(id: &str) -> Result<Option<chain_spec::ChainSpec>, String> {
	Ok(match chain_spec::Alternative::from(id) {
		Some(spec) => Some(spec.load()?),
		None => None,
	})
}
