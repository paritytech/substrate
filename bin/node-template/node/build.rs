use substrate_build_script_utils::{generate_cargo_keys, rerun_if_git_head_changed};
use substrate_wasm_builder::WasmBuilder;

fn main() {
	build_runtime();
	generate_cargo_keys();

	rerun_if_git_head_changed();
}

fn build_runtime() {
	let mut path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
	path.push("../runtime/Cargo.toml");
	WasmBuilder::new()
		.with_project(path.canonicalize().unwrap()).unwrap()
		.export_heap_base()
		.import_memory()
		.build()
}

