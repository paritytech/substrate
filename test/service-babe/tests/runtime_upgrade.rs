// // Copyright 2021 Parity Technologies (UK) Ltd.
// // This file is part of Substrate.

// // Substrate is free software: you can redistribute it and/or modify
// // it under the terms of the GNU General Public License as published by
// // the Free Software Foundation, either version 3 of the License, or
// // (at your option) any later version.

// // Substrate is distributed in the hope that it will be useful,
// // but WITHOUT ANY WARRANTY; without even the implied warranty of
// // MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// // GNU General Public License for more details.

// // You should have received a copy of the GNU General Public License
// // along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

// use cumulus_primitives_core::ParaId;
// use test_service_babe::{initial_head_data, run_relay_chain_validator_node, Keyring::*};
// use futures::{join, StreamExt};
// use sc_client_api::BlockchainEvents;
// use sp_runtime::generic::BlockId;

// #[substrate_test_utils::test]
// #[ignore]
// async fn test_runtime_upgrade() {
// 	let mut builder = sc_cli::LoggerBuilder::new("runtime=debug");
// 	builder.with_colors(false);
// 	let _ = builder.init();

// 	let para_id = ParaId::from(100);
// 	let tokio_handle = tokio::runtime::Handle::current();

// 	// start alice
// 	let alice = run_relay_chain_validator_node(tokio_handle.clone(), Alice, || {}, Vec::new());

// 	// start bob
// 	let bob =
// 		run_relay_chain_validator_node(tokio_handle.clone(), Bob, || {}, vec![alice.addr.clone()]);

// 	// register parachain
// 	alice
// 		.register_parachain(
// 			para_id,
// 			test_runtime_babe::WASM_BINARY
// 				.expect("You need to build the WASM binary to run this test!")
// 				.to_vec(),
// 			initial_head_data(para_id),
// 		)
// 		.await
// 		.unwrap();

// 	// run cumulus charlie (a parachain collator)
// 	let charlie =
// 		test_service_babe::TestNodeBuilder::new(para_id, tokio_handle.clone(), Charlie)
// 			.enable_collator()
// 			.connect_to_relay_chain_nodes(vec![&alice, &bob])
// 			.build()
// 			.await;

// 	// run cumulus dave (a parachain full node)
// 	let dave = test_service_babe::TestNodeBuilder::new(para_id, tokio_handle, Dave)
// 		.connect_to_parachain_node(&charlie)
// 		.connect_to_relay_chain_nodes(vec![&alice, &bob])
// 		.build()
// 		.await;

// 	// Wait for 2 blocks to be produced
// 	charlie.wait_for_blocks(2).await;

// 	let mut expected_runtime_version = charlie
// 		.client
// 		.runtime_version_at(&BlockId::number(0))
// 		.expect("Runtime version exists");
// 	expected_runtime_version.spec_version += 1;

// 	let wasm = test_runtime_babe::wasm_spec_version_incremented::WASM_BINARY
// 		.expect("Wasm binary with incremented spec version should have been built");

// 	// schedule runtime upgrade
// 	charlie.schedule_upgrade(wasm.into()).await.unwrap();

// 	let mut import_stream = dave.client.import_notification_stream();

// 	while let Some(notification) = import_stream.next().await {
// 		if notification.is_new_best {
// 			let runtime_version = dave
// 				.client
// 				.runtime_version_at(&BlockId::Hash(notification.hash))
// 				.expect("Runtime version exists");

// 			if expected_runtime_version == runtime_version {
// 				break
// 			}
// 		}
// 	}

// 	join!(
// 		alice.task_manager.clean_shutdown(),
// 		bob.task_manager.clean_shutdown(),
// 		charlie.task_manager.clean_shutdown(),
// 		dave.task_manager.clean_shutdown(),
// 	);
// }
