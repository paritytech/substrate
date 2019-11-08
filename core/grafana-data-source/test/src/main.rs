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
use std::{
	time::Duration, sync::atomic::{AtomicBool, Ordering}, task::{Context, Poll}, future::Future,
	pin::Pin
};
use rand::Rng;
use futures_util::{FutureExt, future::select};
use tokio::timer::delay_for;

static EXIT: AtomicBool = AtomicBool::new(false);

struct ExitFuture;

impl Future for ExitFuture {
	type Output = ();

	fn poll(self: Pin<&mut Self>, _: &mut Context) -> Poll<Self::Output> {
		let exit = EXIT.load(Ordering::Relaxed);

		println!("Polling, got: {}", exit);

		if exit {
			Poll::Ready(())
		} else {
			Poll::Pending
		}
	}
}

async fn randomness() {
	loop {
		delay_for(Duration::from_secs(1)).await;

		let random = rand::thread_rng().gen_range(0.0, 1000.0);

		record_metrics!(
			"random data" => random,
			"random^2" => random * random
		);
	}
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
	ctrlc::set_handler(|| {
		println!(" - Ctrl-C received");
		EXIT.store(true, Ordering::Relaxed);
	}).unwrap();

	let address = "127.0.0.1:9955".parse().unwrap();

	let server_future = run_server(address).boxed();

	let randomness_future = randomness().boxed();

	select(
		select(randomness_future, server_future),
		ExitFuture
	).await;

	Ok(())
}
