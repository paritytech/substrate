use hoster::run;

fn main() {
	run::<
		node_template_runtime::Block,
		node_template_runtime::RuntimeApi,
		node_template::service::Executor,
		node_template_runtime::GenesisConfig,
		Option<()>,
	>()
	.unwrap();
}
