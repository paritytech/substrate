#![cfg(feature = "rocksdb")]

use log::{warn, info};
use codec::{Decode, Encode, IoReader};
use sp_runtime::{BuildStorage, BenchmarkResults};
use sc_chain_spec::{ChainSpec, RuntimeGenesis, Extension};
use sc_client_db::BenchmarkingState;
use sc_client::ExecutionStrategy;
use sc_executor::{NativeExecutor, NativeExecutionDispatch};
use sp_runtime::{
	traits::{
		Block as BlockT, NumberFor, One, Zero, Header, SaturatedConversion
	}
};
use sp_state_machine::StateMachine;
use sc_cli::WasmExecutionMethod;

use crate::error;

/// Run runtime benchmarks.
pub fn benchmark_runtime<TBl, TExecDisp, G, E> (
	spec: ChainSpec<G, E>,
	strategy: ExecutionStrategy,
	wasm_method: WasmExecutionMethod,
	pallet: String,
	extrinsic: String,
	steps: u32,
	repeat: u32,
) -> error::Result<()> where
	TBl: BlockT,
	TExecDisp: NativeExecutionDispatch + 'static,
	G: RuntimeGenesis,
	E: Extension,
{
	let genesis_storage = spec.build_storage()?;
	let mut changes = Default::default();
	let state = BenchmarkingState::<TBl>::new(genesis_storage)?;
	let executor = NativeExecutor::<TExecDisp>::new(
		wasm_method,
		None, // heap pages
	);
	let result = StateMachine::<_, _, NumberFor<TBl>, _>::new(
		&state,
		None,
		&mut changes,
		&executor,
		"Benchmark_dispatch_benchmark",
		&(&pallet, &extrinsic, steps, repeat).encode(),
		Default::default(),
	).execute(strategy).map_err(|e| format!("Error executing runtime benchmark: {:?}", e))?;
	let results = <Option<Vec<BenchmarkResults>> as Decode>::decode(&mut &result[..]).unwrap_or(None);
	if let Some(results) = results {
		// Print benchmark metadata
		println!("Pallet: {:?}, Extrinsic: {:?}, Steps: {:?}, Repeat: {:?}", pallet, extrinsic, steps, repeat);
		// Print the table header
		results[0].0.iter().for_each(|param| print!("{:?},", param.0));
		print!("time\n");
		// Print the values
		results.iter().for_each(|result| {
			let parameters = &result.0;
			parameters.iter().for_each(|param| print!("{:?},", param.1));
			print!("{:?}\n", result.1);
		});
		info!("Done.");
	} else {
		info!("No Results.");
	}
	Ok(())
}
