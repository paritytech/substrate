use grafana_data_source::{run_server, record_metrics};
use std::{thread::{spawn, sleep}, time::Duration};
use rand::Rng;

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
	hyper::rt::run(run_server(&"127.0.0.1:9955".parse().unwrap()));
	handle.join().unwrap();
}
