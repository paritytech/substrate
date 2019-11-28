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
use std::time::Duration;
use rand::Rng;
use futures::{future::join, executor};

async fn randomness() {
	loop {
		futures_timer::Delay::new(Duration::from_secs(1)).await;

		let random = rand::thread_rng().gen_range(0.0, 1000.0);

		record_metrics!(
			"random data".to_owned() => random,
			"random^2".to_owned() => random * random
		);
	}
}

fn main() {
	executor::block_on(join(
		run_server("127.0.0.1:9955".parse().unwrap()),
		randomness()
	)).0.unwrap();
}
