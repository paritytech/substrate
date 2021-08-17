fn main() {
	substrate_runtime_hoster::Builder::<
		node_runtime::Block,
		node_runtime::RuntimeApi,
		node_executor::Executor,
		node_runtime::GenesisConfig,
		node_cli::chain_spec::Extensions,
	>::new()
	.with_babe_consensus()
	.run()
	.unwrap();
}
