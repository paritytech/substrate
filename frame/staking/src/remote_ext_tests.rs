use remote_externalities::{Builder, Mode, OnlineConfig};
// use sp_runtime::traits::BlakeTwo256;
use sc_executor::{NativeExecutor, WasmExecutionMethod};
use sp_core::storage::well_known_keys;
use sp_runtime::traits::NumberFor;
use sp_state_machine::{ExecutionStrategy, StateMachine};

use crate::mock::*;

const RPC_NODE: &str = "ws://localhost:9944";

// TODO: do I need this feature gat if its in lib where we require this mod?
#[cfg(feature = "remote-ext")]
#[cfg(test)]

// pub type BlockNumber = u32;
// pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
// /// Block type as expected by this runtime.
// pub type Block = generic::Block<Header, UncheckedExtrinsic>;

sc_executor::native_executor_instance!(
	pub MyExecutor,
	substrate_test_runtime::api::dispatch,
	substrate_test_runtime::native_version,
);

#[tokio::test]
async fn test_voter_bags_migration() {
	ExtBuilder::default().build_and_execute(|| {});

	let ext = Builder::<crate::mock::Block>::new()
		.mode(Mode::Online(OnlineConfig {
			transport: RPC_NODE.to_string().into(),
			modules: vec!["Staking".to_string()],
			..Default::default()
		}))
		// TODO inject code from this runtime????
		.inject_hashed_key(well_known_keys::CODE)
		.build()
		.await
		.unwrap();

	ext.execute_with(|| {
		// - check existing data ??
		// - regenerate ...
		// - check regenerated data
		// - stats on how each bag is occupied?
		// - use real thresholds ..
		// any other test we need to ...
	})

	// let executor =
	// 	NativeExecutor::<MyExecutor>::new(WasmExecutionMethod::Interpreted, Some(2046), 8);

	// let mut changes = Default::default();

	// // TODO probs don't call StateMachine here, instead 
	// let _encoded_result = StateMachine::<_, _, NumberFor<Block>, _>::new(
	// 	&ext.backend,
	// 	None,
	// 	&mut changes,
	// 	&executor,
	// 	"TryRuntime_on_runtime_upgrade",
	// 	&[],
	// 	ext.extensions,
	// 	&sp_state_machine::backend::BackendRuntimeCode::new(&ext.backend)
	// 		.runtime_code()
	// 		.unwrap(),
	// 	sp_core::testing::TaskExecutor::new(),
	// )
	// .execute(ExecutionStrategy::AlwaysWasm.into())
	// .map_err(|e| format!("failed to execute 'TryRuntime_on_runtime_upgrade': {:?}", e))
	// .unwrap();
	// // .unwrap();
}
