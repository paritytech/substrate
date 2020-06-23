use std::fs::{File, OpenOptions};
use std::io::prelude::*;
use frame_benchmarking::{BenchmarkBatch, BenchmarkSelector, Analysis};

pub fn open_file() -> Result<File, std::io::Error> {
	File::create("benchmarks.rs")
}

pub fn write_results(file: &mut File, batches: Result<Vec<BenchmarkBatch>, String>) -> Result<(), std::io::Error> {
	let batches = batches.unwrap();
	//let f = &mut std::fmt::Formatter::new();
	batches.iter().for_each(|batch| {
		// function name
		write!(file, "pub fn {}_{}(",
			String::from_utf8(batch.pallet.clone()).unwrap(),
			String::from_utf8(batch.benchmark.clone()).unwrap()
		).unwrap();

		// params
		let components = &batch.results[0].components;
		for component in components {
			write!(file, "{:?}: u32, ", component.0).unwrap();
		}
		// return value
		write!(file, ") -> Weight {{\n").unwrap();

		let extrinsic_time = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::ExtrinsicTime).unwrap();
		write!(file, "	({} as Weight)\n", extrinsic_time.base).unwrap();
		extrinsic_time.slopes.iter().zip(extrinsic_time.names.iter()).for_each(|(name, slope)| {
			write!(file, "		.saturating_add(({} as Weight).saturating_mul({} as Weight))\n",
				name,
				slope,
			).unwrap();
		});

		let reads = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Reads).unwrap();
		write!(file, "		.saturating_add(T::DbWeight::get().reads({}))\n", reads.base).unwrap();
		reads.slopes.iter().zip(reads.names.iter()).for_each(|(name, slope)| {
			write!(file, "		.saturating_add(T::DbWeight::get().reads(({} as Weight).saturating_mul({} as Weight))\n",
				name,
				slope,
			).unwrap();
		});

		let writes = Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Writes).unwrap();
		write!(file, "		.saturating_add(T::DbWeight::get().writes({}))\n", writes.base).unwrap();
		writes.slopes.iter().zip(writes.names.iter()).for_each(|(name, slope)| {
			write!(file, "		.saturating_add(T::DbWeight::get().writes(({} as Weight).saturating_mul({} as Weight))\n",
				name,
				slope,
			).unwrap();
		});

		// close function
		write!(file, "}}\n").unwrap();



	});

	Ok(())
}
