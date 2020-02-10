#![cfg(feature = "rocksdb")]

use std::fmt::Debug;
use structopt::StructOpt;
use sc_service::{
	Configuration, ChainSpecExtension, RuntimeGenesis, ServiceBuilderCommand,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use crate::error;
use crate::execution_strategy::ExecutionStrategy;
use crate::params::{WasmExecutionMethod, SharedParams};

/// The `benchmark` command used to benchmark FRAME Pallets.
#[derive(Debug, StructOpt, Clone)]
pub struct BenchmarkCmd {
	/// Select a FRAME Pallet to benchmark.
	#[structopt(short, long)]
	pub pallet: String,

	/// Select an extrinsic to benchmark.
	#[structopt(short, long)]
	pub extrinsic: String,

	/// Select how many samples we should take across the variable components.
	#[structopt(short, long, default_value = "1")]
	pub steps: u32,

	/// Select how many repetitions of this benchmark should run.
	#[structopt(short, long, default_value = "1")]
	pub repeat: u32,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	/// The execution strategy that should be used for benchmarks
	#[structopt(
		long = "execution",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
	)]
	pub execution: Option<ExecutionStrategy>,

	/// Method for executing Wasm runtime code.
	#[structopt(
		long = "wasm-execution",
		value_name = "METHOD",
		possible_values = &WasmExecutionMethod::enabled_variants(),
		case_insensitive = true,
		default_value = "Interpreted"
	)]
	pub wasm_method: WasmExecutionMethod,
}

impl BenchmarkCmd {
	/// Runs the command and benchmarks the chain.
	pub fn run<G, E, B, BC, BB>(
		self,
		config: Configuration<G, E>,
		_builder: B,
	) -> error::Result<()>
	where
		B: FnOnce(Configuration<G, E>) -> Result<BC, sc_service::error::Error>,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		BC: ServiceBuilderCommand<Block = BB> + Unpin,
		BB: sp_runtime::traits::Block + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
	{
		let spec = config.chain_spec.expect("chain_spec is always Some");
		let execution_strategy = self.execution.unwrap_or(ExecutionStrategy::Native).into();
		let wasm_method = self.wasm_method.into();
		let pallet = self.pallet;
		let extrinsic = self.extrinsic;
		let steps = self.steps;
		let repeat = self.repeat;
		sc_service::chain_ops::benchmark_runtime::<BB, BC::NativeDispatch, _, _>(spec, execution_strategy, wasm_method, pallet, extrinsic, steps, repeat)?;
		Ok(())
	}
}
