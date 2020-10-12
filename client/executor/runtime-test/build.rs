// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use wasm_builder_runner::WasmBuilder;

fn main() {
	// regular build
	WasmBuilder::new()
		.with_current_project()
		.with_wasm_builder_from_crates_or_path("2.0.1", "../../../utils/wasm-builder")
		.export_heap_base()
		.import_memory()
		.build();

	// and building with tracing activated
	WasmBuilder::new()
		.with_current_project()
		.with_wasm_builder_from_crates_or_path("2.0.1", "../../../utils/wasm-builder")
		.export_heap_base()
		.import_memory()
		.set_file_name("wasm_binary_with_tracing.rs")
		.append_to_rust_flags("--cfg feature=\\\"with-tracing\\\"")
		.build();
}
