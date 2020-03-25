use sc_cli::RunCmd;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
pub struct Cli {
	#[structopt(subcommand)]
	pub subcommand: Option<Subcommand>,

	#[structopt(flatten)]
	pub run: RunCmd,
}

/// Possible subcommands of the main binary.
#[derive(Clone, Debug, StructOpt)]
pub enum Subcommand {
	/// A set of base subcommands handled by `sc_cli`.
	#[structopt(flatten)]
	Base(sc_cli::Subcommand),

}
