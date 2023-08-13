// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use assert_cmd::cargo::cargo_bin;
use std::{process, time::Duration};

use crate::common::KillChildOnDrop;

use substrate_cli_test_utils as common;
pub mod websocket_server;

#[tokio::test]
async fn telemetry_works() {
	common::run_with_timeout(Duration::from_secs(60 * 10), async move {
		let config = websocket_server::Config {
			capacity: 1,
			max_frame_size: 1048 * 1024,
			send_buffer_len: 32,
			bind_address: "127.0.0.1:0".parse().unwrap(),
		};
		let mut server = websocket_server::WsServer::new(config).await.unwrap();

		let addr = server.local_addr().unwrap();

		let server_task = tokio::spawn(async move {
			loop {
				use websocket_server::Event;
				match server.next_event().await {
					// New connection on the listener.
					Event::ConnectionOpen { address } => {
						println!("New connection from {:?}", address);
						server.accept();
					},

					// Received a message from a connection.
					Event::BinaryFrame { message, .. } => {
						let json: serde_json::Value = serde_json::from_slice(&message).unwrap();
						let object =
							json.as_object().unwrap().get("payload").unwrap().as_object().unwrap();
						if matches!(object.get("best"), Some(serde_json::Value::String(_))) {
							break
						}
					},

					Event::TextFrame { .. } => {
						panic!("Got a TextFrame over the socket, this is a bug")
					},

					// Connection has been closed.
					Event::ConnectionError { .. } => {},
				}
			}
		});

		let mut substrate = process::Command::new(cargo_bin("substrate-node"));

		let mut substrate = KillChildOnDrop(
			substrate
				.args(&["--dev", "--tmp", "--telemetry-url"])
				.arg(format!("ws://{} 10", addr))
				.arg("--no-hardware-benchmarks")
				.stdout(process::Stdio::piped())
				.stderr(process::Stdio::piped())
				.stdin(process::Stdio::null())
				.spawn()
				.unwrap(),
		);

		server_task.await.expect("server task panicked");

		substrate.assert_still_running();

		// Stop the process
		substrate.stop();
	})
	.await;
}
