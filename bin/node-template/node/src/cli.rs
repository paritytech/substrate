use sc_cli::RunCmd;
use clap::Parser;

#[derive(Debug, Parser)]
pub struct Cli {
	#[clap(subcommand)]
	pub subcommand: Subcommands,
}

#[derive(Debug, clap::Subcommand)]
pub enum Subcommands {
	#[clap(flatten)]
	SubcommandA(SubcommandA),
	SubcommandB(SubcommandB),
}

#[derive(Debug, clap::Subcommand)]
pub enum SubcommandA {
	#[clap(subcommand)]
	Key(sc_cli::KeySubcommand),
}

#[derive(Debug, Parser)]
pub struct SubcommandB {
	#[clap(subcommand)]
	pub subcommand: Option<Subcommand>,

	#[clap(flatten)]
	pub run: RunCmd,
}

#[derive(Debug, clap::Subcommand)]
pub enum Subcommand {
	/// Build a chain specification.
	BuildSpec(sc_cli::BuildSpecCmd),

	/// Validate blocks.
	CheckBlock(sc_cli::CheckBlockCmd),

	/// Export blocks.
	ExportBlocks(sc_cli::ExportBlocksCmd),

	/// Export the state of a given block into a chain spec.
	ExportState(sc_cli::ExportStateCmd),

	/// Import blocks.
	ImportBlocks(sc_cli::ImportBlocksCmd),

	/// Remove the whole chain.
	PurgeChain(sc_cli::PurgeChainCmd),

	/// Revert the chain to a previous state.
	Revert(sc_cli::RevertCmd),

	/// Sub-commands concerned with benchmarking.
	#[clap(subcommand)]
	Benchmark(frame_benchmarking_cli::BenchmarkCmd),

	/// Try some command against runtime state.
	#[cfg(feature = "try-runtime")]
	TryRuntime(try_runtime_cli::TryRuntimeCmd),

	/// Try some command against runtime state. Note: `try-runtime` feature must be enabled.
	#[cfg(not(feature = "try-runtime"))]
	TryRuntime,

	/// Db meta columns information.
	ChainInfo(sc_cli::ChainInfoCmd),
}
