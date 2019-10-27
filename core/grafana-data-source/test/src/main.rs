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
use std::{thread::{spawn, sleep}, time::Duration};
use rand::Rng;

// futures::future::empty is not cloneable.
#[derive(Clone)]
struct EmptyFuture;

impl futures::Future for EmptyFuture {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> futures::Poll<(), ()> {
		Ok(futures::Async::NotReady)
	}
}

fn main() {
	let handle = spawn(|| {
		let mut rng = rand::thread_rng();

		loop {
			let random = rng.gen_range(0.0, 1000.0);
			record_metrics!(
                "random data" => random,
                "random^2" => random * random
            );
			sleep(Duration::from_secs(1));
		}
	});
	hyper::rt::run(run_server(&"127.0.0.1:9955".parse().unwrap(), EmptyFuture));
	handle.join().unwrap();
}
