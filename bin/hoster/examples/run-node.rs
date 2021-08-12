use hoster::run;

fn main() {
	run::<
		node_runtime::Block,
		node_runtime::RuntimeApi,
		node_executor::Executor,
		node_runtime::GenesisConfig,
		node_cli::chain_spec::Extensions,
	>()
	.unwrap();
}
