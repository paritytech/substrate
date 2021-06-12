// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Tests that are only relevant for Linux.

// Constrain this only to wasmtime for the time being. Without this rustc will complain on unused
// imports and items. The alternative is to plop `cfg(feature = wasmtime)` everywhere which seems
// borthersome.
#![cfg(feature = "wasmtime")]

use crate::WasmExecutionMethod;
use super::mk_test_runtime;
use codec::Encode as _;

mod smaps;

use self::smaps::Smaps;

#[test]
fn memory_consumption_compiled() {
	use sc_executor_common::wasm_runtime::WasmModule as _;

	let runtime = mk_test_runtime(WasmExecutionMethod::Compiled, 1024);

	let instance = runtime.new_instance().unwrap();
	let heap_base = instance
		.get_global_const("__heap_base")
		.expect("`__heap_base` is valid")
		.expect("`__heap_base` exists")
		.as_i32()
		.expect("`__heap_base` is an `i32`");

	let smaps = Smaps::new();

	instance
		.call_export(
			"test_dirty_plenty_memory",
			&(heap_base as u32, 1u32).encode(),
		)
		.unwrap();

	// Just assume that the linear memory is backed by a single memory mapping.
	let base_addr = instance.linear_memory_base_ptr().unwrap() as usize;
	let rss_pre = smaps.get_rss(base_addr).unwrap();

	instance
		.call_export(
			"test_dirty_plenty_memory",
			&(heap_base as u32, 1024u32).encode(),
		)
		.unwrap();
	let rss_post = smaps.get_rss(base_addr).unwrap();

	assert_eq!(rss_post.saturating_sub(rss_pre), 0);
}
