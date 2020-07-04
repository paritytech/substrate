use wasm_builder_runner::WasmBuilder;

fn main() {
	WasmBuilder::new()
		.with_current_project()
		.with_wasm_builder_from_crates_or_path("1.0.11", "../../../utils/wasm-builder")
		.export_heap_base()
		.import_memory()
		.build()
}
