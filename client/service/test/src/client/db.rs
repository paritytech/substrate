// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use sp_core::offchain::{OffchainStorage, storage::InMemOffchainStorage};
use std::sync::Arc;

type TestBackend = sc_client_api::in_mem::Backend<substrate_test_runtime::Block>;

#[test]
fn test_leaves_with_complex_block_tree() {
	let backend = Arc::new(TestBackend::new());

	substrate_test_runtime_client::trait_tests::test_leaves_for_backend(backend);
}

#[test]
fn test_blockchain_query_by_number_gets_canonical() {
	let backend = Arc::new(TestBackend::new());

	substrate_test_runtime_client::trait_tests::test_blockchain_query_by_number_gets_canonical(backend);
}

#[test]
fn in_memory_offchain_storage() {

	let mut storage = InMemOffchainStorage::default();
	assert_eq!(storage.get(b"A", b"B"), None);
	assert_eq!(storage.get(b"B", b"A"), None);

	storage.set(b"A", b"B", b"C");
	assert_eq!(storage.get(b"A", b"B"), Some(b"C".to_vec()));
	assert_eq!(storage.get(b"B", b"A"), None);

	storage.compare_and_set(b"A", b"B", Some(b"X"), b"D");
	assert_eq!(storage.get(b"A", b"B"), Some(b"C".to_vec()));
	storage.compare_and_set(b"A", b"B", Some(b"C"), b"D");
	assert_eq!(storage.get(b"A", b"B"), Some(b"D".to_vec()));

	assert!(!storage.compare_and_set(b"B", b"A", Some(b""), b"Y"));
	assert!(storage.compare_and_set(b"B", b"A", None, b"X"));
	assert_eq!(storage.get(b"B", b"A"), Some(b"X".to_vec()));
}
