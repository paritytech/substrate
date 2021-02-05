#![cfg(unix)]

use assert_cmd::cargo::cargo_bin;
use futures::prelude::*;
use nix::sys::signal::{kill, Signal::SIGINT};
use nix::unistd::Pid;
use std::convert::TryInto;
use std::process;
use tempfile::tempdir;

pub mod common;
pub mod websocket_server;

#[async_std::test]
async fn telemetry_works() {
	let config = websocket_server::Config {
		capacity: 1,
		max_frame_size: 1048 * 1024,
		send_buffer_len: 32,
		bind_address: "127.0.0.1:0".parse().unwrap(),
	};
	let mut server = websocket_server::WsServer::new(config).await.unwrap();

	let addr = server.local_addr().unwrap();

	let server_task = async_std::task::spawn(async move {
		loop {
			use websocket_server::Event;

			let mut received_telemetry = false;

			match server.next_event().await {
				// New connection on the listener.
				Event::ConnectionOpen { address } => {
					println!("New connection from {:?}", address);
					if server.len() < 512 {
						// Rather than passing `()`, it is possible to pass any value. The value is
						// provided back on `TextFrame` and `ConnectionError` events.
						server.accept(());
					} else {
						server.reject();
					}
				}

				// Received a message from a connection.
				Event::TextFrame { message, .. } => {
					let json: serde_json::Value = serde_json::from_str(&message).unwrap();
					let object = json.as_object().unwrap();
					let payload = object.get("payload").unwrap();
					let object = payload.as_object().unwrap();
					if matches!(object.get("best"), Some(serde_json::Value::String(_))) {
						received_telemetry = true;
					}
					//println!("Received message: {}", json);
				}

				// Connection has been closed.
				Event::ConnectionError { .. } => {}
			}

			if received_telemetry {
				break;
			}
		}
	});

	let base_path = tempdir().expect("could not create a temp dir");
	let mut substrate = process::Command::new(cargo_bin("substrate"));

	let mut substrate = substrate
		.args(&["--dev", "--telemetry-url"])
		.arg(format!("ws://{} 10", addr))
		.arg("-d")
		.arg(base_path.path())
		.stdout(process::Stdio::piped())
		.stderr(process::Stdio::piped())
		.stdin(process::Stdio::null())
		.spawn()
		.unwrap();

	server_task.await;

	assert!(
		substrate.try_wait().unwrap().is_none(),
		"the process should still be running"
	);

	// Stop the process
	kill(Pid::from_raw(substrate.id().try_into().unwrap()), SIGINT).unwrap();
	assert!(common::wait_for(&mut substrate, 40)
		.map(|x| x.success())
		.unwrap_or_default());

	let output = substrate.wait_with_output().unwrap();

	println!("{}", String::from_utf8(output.stdout).unwrap());
	eprintln!("{}", String::from_utf8(output.stderr).unwrap());
	assert!(output.status.success());
}
