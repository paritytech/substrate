// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use substrate_wasm_builder::WasmBuilder;

fn main() {
	// regular build
	WasmBuilder::new()
		.with_current_project()
		.export_heap_base()
		.import_memory()
		.build();

	// and building with tracing activated
	WasmBuilder::new()
		.with_current_project()
		.export_heap_base()
		.import_memory()
		.set_file_name("wasm_binary_with_tracing.rs")
		.append_to_rust_flags(r#"--cfg feature="with-tracing""#)
		.build();
}
