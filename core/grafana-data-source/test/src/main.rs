// Copyright 2019 Parity Technologies (UK) Ltd.
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

use grafana_data_source::{run_server, record_metrics};
use std::{time::Duration, sync::atomic::{AtomicBool, Ordering}};
use rand::Rng;
use futures::{Async, Future, Stream};
use stream_cancel::StreamExt;
use tokio::{runtime::Runtime, timer::Interval};

static EXIT: AtomicBool = AtomicBool::new(false);

struct ExitFuture;

impl futures::Future for ExitFuture {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> futures::Poll<(), ()> {
		let value = EXIT.load(Ordering::Relaxed);

		println!("Polling, got: {}", value);

		if value {
			Ok(Async::Ready(()))
		} else {
			Ok(Async::NotReady)
		}
	}
}

fn main() {
	ctrlc::set_handler(|| {
		println!(" - Ctrl-C received");
		EXIT.store(true, Ordering::Relaxed);
	}).unwrap();

	let address = "127.0.0.1:9955".parse().unwrap();

	let randomness_future = Interval::new_interval(Duration::from_secs(1))
		.take_until(ExitFuture)
		.for_each(move |_| {
			let random = rand::thread_rng().gen_range(0.0, 1000.0);
			record_metrics!(
				"random data" => random,
				"random^2" => random * random
			);
			futures::future::ok(())
		})
		.map_err(|_| ())
		.map(|_| println!("Shutting down randomness future"));

	let server_future = run_server(&address, ExitFuture)
		.map(|_| println!("Shutting down server future"));

	let mut rt = Runtime::new().unwrap();

	rt.spawn(randomness_future);
	rt.spawn(server_future);

	rt.shutdown_on_idle().wait().unwrap();
}
