// // Copyright 2020-2021 Parity Technologies (UK) Ltd.
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
// use cumulus_test_service::{initial_head_data, run_relay_chain_validator_node, Keyring::*};
// use futures::join;

// #[substrate_test_utils::test]
// #[ignore]
// async fn test_collating_and_non_collator_mode_catching_up() {
// 	let mut builder = sc_cli::LoggerBuilder::new("");
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
// 			cumulus_test_runtime::WASM_BINARY
// 				.expect("You need to build the WASM binary to run this test!")
// 				.to_vec(),
// 			initial_head_data(para_id),
// 		)
// 		.await
// 		.unwrap();

// 	// run cumulus charlie (a parachain collator)
// 	let charlie =
// 		cumulus_test_service::TestNodeBuilder::new(para_id, tokio_handle.clone(), Charlie)
// 			.enable_collator()
// 			.connect_to_relay_chain_nodes(vec![&alice, &bob])
// 			.build()
// 			.await;
// 	charlie.wait_for_blocks(5).await;

// 	// run cumulus dave (a parachain full node) and wait for it to sync some blocks
// 	let dave = cumulus_test_service::TestNodeBuilder::new(para_id, tokio_handle, Dave)
// 		.connect_to_parachain_node(&charlie)
// 		.connect_to_relay_chain_nodes(vec![&alice, &bob])
// 		.build()
// 		.await;
// 	dave.wait_for_blocks(7).await;

// 	join!(
// 		alice.task_manager.clean_shutdown(),
// 		bob.task_manager.clean_shutdown(),
// 		charlie.task_manager.clean_shutdown(),
// 		dave.task_manager.clean_shutdown(),
// 	);
// }
