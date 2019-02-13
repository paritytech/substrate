// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Substrate Node CLI

#![warn(missing_docs)]

extern crate ctrlc;
extern crate futures;
extern crate libc;

use cli::VersionInfo;
use futures::sync::oneshot;
use futures::{future, Future};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::{thread, time};


struct Exit {
	pub exit: oneshot::Receiver<()>,
}

impl cli::IntoExit for Exit {
	type Exit = future::MapErr<oneshot::Receiver<()>, fn(oneshot::Canceled) -> ()>;
	fn into_exit(self) -> Self::Exit {
		self.exit.map_err(drop)
	}
}

unsafe fn abort(process_id: libc::pid_t) {
	libc::kill(process_id, libc::SIGTERM);
}

fn main() -> cli::error::Result<()> {
	println!("Chaos");
	unsafe {
		let mut nodes: Vec<libc::pid_t> = vec![];
		for i in 30333..30346 {
		    match libc::fork() {
		        -1 => {
					println!("fork failed");
				},
		        0 => {
					let args = if i == 30333 {
						vec![
							"target/release/substrate".to_string(),
							"--base-path".to_string(), "/tmp/alice".to_string(),
							"--name".to_string(), "Alice".to_string(),
							"--key".to_string(), "Alice".to_string(),
							"--chain=local".to_string(),
							"--node-key".to_string(), "0000000000000000000000000000000000000000000000000000000000000001".to_string(),
							"--validator".to_string(),
						]
					} else {
						vec![
							"target/release/substrate".to_string(),
							"--base-path".to_string(), format!("/tmp/BOB-{:?}", i),
							"--name".to_string(), format!("/tmp/BOB-{:?}", i),
							"--key".to_string(), format!("/tmp/BOB-{:?}", i),
							"--port".to_string(), format!("{:?}", i),
							"--bootnodes".to_string(), "/ip4/127.0.0.1/tcp/30333/p2p/QmQZ8TjTqeDj3ciwr93EJ95hxfDsb9pEYDizUAbWpigtQN".to_string(),
							"--chain=local".to_string(),
							"--validator".to_string(),
						]
					};
					let _ = thread::Builder::new()
						.name("Monitor".into())
						.spawn(move || {
							loop {
								let version = VersionInfo {
									name: "Substrate Node",
									commit: env!("VERGEN_SHA_SHORT"),
									version: env!("CARGO_PKG_VERSION"),
									executable_name: "substrate",
									author: "Parity Technologies <admin@parity.io>",
									description: "Generic substrate node",
									support_url: "https://github.com/paritytech/substrate/issues/new",
								};
								let (_exit_send, exit) = oneshot::channel();
								let exit = Exit { exit: exit };
								let args_clone = args.clone();
								let handle = thread::Builder::new()
									.name("Restart node".into())
									.spawn(move || {
										println!("Starting");
										let _ = cli::run(args_clone, exit, version).unwrap();
										println!("Stopped");
									})
									.expect("Node thread spawning failed");
								//thread::sleep(time::Duration::new(5, 0));
								//exit_send.send(()).expect("Failed to send exit");
								let _ = handle.join();
								// Wait a little bit before restarting.
								//thread::sleep(time::Duration::new(60, libc::rand() as u32));
							}

						})
						.expect("Monitor thread spawning failed");
		            //let _ = cli::run(args_clone, exit, version).unwrap();
					loop {
						// Keep the main thread alive.
						thread::sleep(time::Duration::new(1, 0));
					}
		        },
		        pid => {
					nodes.push(pid);
				},
		    }
		}
		println!("Processes: {:?}", nodes);
		let running = Arc::new(AtomicBool::new(true));
		let r = running.clone();
		ctrlc::set_handler(move || {
			for process_id in nodes.iter() {
				abort(process_id.clone());
			}
			r.store(false, Ordering::SeqCst);
		}).expect("Error setting Ctrl-C handler");
		while running.load(Ordering::SeqCst) {
			// Wait a little bit
			thread::sleep(time::Duration::new(1, 0));
		}
	}
	Ok(())
}
