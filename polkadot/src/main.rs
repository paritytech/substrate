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
extern crate polkadot_service as service;
extern crate ctrlc;
extern crate futures;

use futures::mpsc;

// the regular polkadot application simply runs until ctrl-c
struct Application;
impl cli::Application for Application {
	type Work = mpsc::Receiver<()>;

	fn work<C: service::Components>(self, _service: Service<C>) -> Self::Work {
		// can't use signal directly here because CtrlC takes only `Fn`.
		let (exit_send, exit) = mpsc::channel(1);
		ctrlc::CtrlC::set_handler(move || {
			exit_send.clone().send(()).wait().expect("Error sending exit notification");
		});

		exit
	}
}

#[macro_use]
extern crate error_chain;

quick_main!(run);

fn run() -> cli::error::Result<()> {
	cli::run(::std::env::args())
}
