mod runtime;

pub use self::runtime::Ext;

use self::runtime::env_def::FunctionImplProvider;

pub type StorageKey = [u8; 32];

pub struct MemorySchedule {
	pub initial: u32,
	pub maximum: Option<u32>,
}

pub fn execute<E: Ext>(
	code: &[u8],
	entrypoint_name: &'static str,
	mut ext: E,
	input_data: Vec<u8>,
	memory_schedule: &MemorySchedule,
) {
	let memory = sp_sandbox::Memory::new(memory_schedule.initial, memory_schedule.maximum)
		.unwrap_or_else(|_| {
			// unlike `.expect`, explicit panic preserves the source location.
			// Needed as we can't use `RUST_BACKTRACE` in here.
			panic!(
				"exec.prefab_module.initial can't be greater than exec.prefab_module.maximum;
						thus Memory::new must not fail;
						qed"
			)
		});

	let mut imports = sp_sandbox::EnvironmentDefinitionBuilder::new();
	imports.add_memory("env", "memory", memory.clone());
	runtime::Env::impls(&mut |name, func_ptr| {
		imports.add_host_func("env", name, func_ptr);
	});

	let mut runtime = runtime::Runtime::new(
		&mut ext,
		input_data,
		memory,
	);

	sp_sandbox::Instance::new(code, &imports, &mut runtime)
		.and_then(|mut instance| instance.invoke(entrypoint_name, &[], &mut runtime));
}
