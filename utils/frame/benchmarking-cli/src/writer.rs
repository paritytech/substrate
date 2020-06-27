use std::fs::File;
use std::io::prelude::*;
use frame_benchmarking::{BenchmarkBatch, BenchmarkSelector, Analysis};

fn uppercase_first_letter(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
    }
}

pub fn open_file() -> Result<File, std::io::Error> {
	File::create("benchmarks.rs")
}

pub fn write_results(file: &mut File, batches: Result<Vec<BenchmarkBatch>, String>) -> Result<(), std::io::Error> {
	let batches = batches.unwrap();

	let mut current_pallet = Vec::<u8>::new();

	// general imports
	write!(file, "use frame_support::weights::{{Weight, constants::RocksDbWeight}};\n").unwrap();

	batches.iter().for_each(|batch| {

		let pallet_string = String::from_utf8(batch.pallet.clone()).unwrap();
		let benchmark_string = String::from_utf8(batch.benchmark.clone()).unwrap();

		// only create new trait definitions when we go to a new pallet
		if batch.pallet != current_pallet {
			if !current_pallet.is_empty() {
				// close trait
				write!(file, "}}\n").unwrap();
			}

			// pallet trait import
			write!(file, "use pallet_{}::{}Weight;\n",
				pallet_string,
				uppercase_first_letter(&pallet_string),
			).unwrap();

			// struct for weights
			write!(file, "pub struct WeightFor{};\n",
				uppercase_first_letter(&pallet_string),
			).unwrap();

			// trait wrapper
			write!(file, "impl {}Weight for WeightFor{} {{\n",
				uppercase_first_letter(&pallet_string),
				uppercase_first_letter(&pallet_string),
			).unwrap();

			current_pallet = batch.pallet.clone()
		}

		// function name
		write!(file, "	fn {}(", benchmark_string).unwrap();

		// params
		let components = &batch.results[0].components;
		for component in components {
			write!(file, "{:?}: u32, ", component.0).unwrap();
		}
		// return value
		write!(file, ") -> Weight {{\n").unwrap();

		let extrinsic_time = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::ExtrinsicTime).unwrap();
		write!(file, "		({} as Weight)\n", extrinsic_time.base.saturating_mul(1000)).unwrap();
		extrinsic_time.slopes.iter().zip(extrinsic_time.names.iter()).for_each(|(slope, name)| {
			write!(file, "			.saturating_add(({} as Weight).saturating_mul({} as Weight))\n",
				slope.saturating_mul(1000),
				name,
			).unwrap();
		});

		let reads = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Reads).unwrap();
		write!(file, "			.saturating_add(RocksDbWeight::get().reads({} as Weight))\n", reads.base).unwrap();
		reads.slopes.iter().zip(reads.names.iter()).for_each(|(slope, name)| {
			write!(file, "			.saturating_add(RocksDbWeight::get().reads(({} as Weight).saturating_mul({} as Weight)))\n",
				slope,
				name,
			).unwrap();
		});

		let writes = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Writes).unwrap();
		write!(file, "			.saturating_add(RocksDbWeight::get().writes({} as Weight))\n", writes.base).unwrap();
		writes.slopes.iter().zip(writes.names.iter()).for_each(|(slope, name)| {
			write!(file, "			.saturating_add(RocksDbWeight::get().writes(({} as Weight).saturating_mul({} as Weight)))\n",
				slope,
				name,
			).unwrap();
		});

		// close function
		write!(file, "	}}\n").unwrap();
	});

	// final close trait
	write!(file, "}}\n").unwrap();

	Ok(())
}
