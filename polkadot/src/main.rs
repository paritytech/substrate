// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Polkadot CLI

#![warn(missing_docs)]

extern crate polkadot_cli as cli;
extern crate ctrlc;
extern crate futures;

#[macro_use]
extern crate error_chain;

use cli::{ServiceComponents, Service, VersionInfo};
use futures::sync::oneshot;
use futures::{future, Future};

use std::cell::RefCell;

mod vergen {
	#![allow(unused)]
	include!(concat!(env!("OUT_DIR"), "/version.rs"));
}

// the regular polkadot worker simply does nothing until ctrl-c
struct Worker;
impl cli::IntoExit for Worker {
	type Exit = future::MapErr<oneshot::Receiver<()>, fn(oneshot::Canceled) -> ()>;
	fn into_exit(self) -> Self::Exit {
		// can't use signal directly here because CtrlC takes only `Fn`.
		let (exit_send, exit) = oneshot::channel();

		let exit_send_cell = RefCell::new(Some(exit_send));
		ctrlc::CtrlC::set_handler(move || {
			if let Some(exit_send) = exit_send_cell.try_borrow_mut().expect("signal handler not reentrant; qed").take() {
				exit_send.send(()).expect("Error sending exit notification");
			}
		});

		exit.map_err(drop)
	}
}

impl cli::Worker for Worker {
	type Work = <Self as cli::IntoExit>::Exit;
	fn work<C: ServiceComponents>(self, _service: &Service<C>) -> Self::Work {
		use cli::IntoExit;
		self.into_exit()
	}
}

quick_main!(run);

fn run() -> cli::error::Result<()> {
	let version = VersionInfo {
		commit: vergen::short_sha(),
		version: env!("CARGO_PKG_VERSION"),
		executable_name: "polkadot",
		author: "Parity Team <admin@parity.io>",
		description: "Polkadot Node Rust Implementation",
	};
	cli::run(::std::env::args(), Worker, version)
}
