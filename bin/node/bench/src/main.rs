#[macro_use] mod core;
mod import;

use crate::core::run_benchmark;
use import::ImportBenchmarkDescription;
use node_testing::bench::{Profile, KeyTypes};
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "node-bench", about = "Node integration benchmarks")]
struct Opt {
    #[structopt(short, long)]
    list: bool,

    #[structopt(short, long)]
    json: bool,

    filter: Option<String>,
}

fn main() {
    let opt = Opt::from_args();

    if !opt.json {
        sc_cli::init_logger("");
    }

    let mut benchmarks = matrix!(
        profile in [Profile::Wasm, Profile::Native] =>
            ImportBenchmarkDescription {
                profile: *profile,
                key_types: KeyTypes::Sr25519,
            }
    );

    benchmarks.extend(matrix!(
        ImportBenchmarkDescription {
            profile: Profile::Native,
            key_types: KeyTypes::Ed25519,
        }
    ));

    if opt.list {
        for benchmark in benchmarks.iter() {
            log::info!("{}: {}", benchmark.name(), benchmark.path().full())
        }
        return;
    }

    let mut results = Vec::new();
    for benchmark in benchmarks {
        if opt.filter.as_ref().map(|f| benchmark.path().has(f)).unwrap_or(true) {
            log::info!("Starting {}", benchmark.name());
            let result = run_benchmark(benchmark);
            log::info!("{}", result);

            results.push(result);
        }
    }

    if opt.json {
        let json_result: String = serde_json::to_string(&results).expect("Failed to construct json");
        println!("{}", json_result);
    }

}