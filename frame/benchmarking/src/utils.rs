// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Interfaces, types and utils for benchmarking a FRAME runtime.

use codec::{Encode, Decode};
use sp_std::{vec::Vec, prelude::Box};
use sp_io::hashing::blake2_256;
use sp_runtime::RuntimeString;

/// An alphabet of possible parameters to use for benchmarking.
#[derive(Encode, Decode, Clone, Copy, PartialEq, Debug)]
#[allow(missing_docs)]
#[allow(non_camel_case_types)]
pub enum BenchmarkParameter {
	a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z,
}

/// The results of a single of benchmark.
#[derive(Encode, Decode, Clone, PartialEq, Debug)]
pub struct BenchmarkBatch {
	/// The pallet containing this benchmark.
	pub pallet: Vec<u8>,
	/// The extrinsic (or benchmark name) of this benchmark.
	pub benchmark: Vec<u8>,
	/// The results from this benchmark.
	pub results: Vec<BenchmarkResults>,
}

/// Results from running benchmarks on a FRAME pallet.
/// Contains duration of the function call in nanoseconds along with the benchmark parameters
/// used for that benchmark result.
#[derive(Encode, Decode, Default, Clone, PartialEq, Debug)]
pub struct BenchmarkResults {
	pub components: Vec<(BenchmarkParameter, u32)>,
	pub extrinsic_time: u128,
	pub storage_root_time: u128,
	pub reads: u32,
	pub repeat_reads: u32,
	pub writes: u32,
	pub repeat_writes: u32,
}

sp_api::decl_runtime_apis! {
	/// Runtime api for benchmarking a FRAME runtime.
	pub trait Benchmark {
		/// Dispatch the given benchmark.
		fn dispatch_benchmark(
			pallet: Vec<u8>,
			benchmark: Vec<u8>,
			lowest_range_values: Vec<u32>,
			highest_range_values: Vec<u32>,
			steps: Vec<u32>,
			repeat: u32,
		) -> Result<Vec<BenchmarkBatch>, RuntimeString>;
	}
}

/// Interface that provides functions for benchmarking the runtime.
#[sp_runtime_interface::runtime_interface]
pub trait Benchmarking {
	/// Get the number of nanoseconds passed since the UNIX epoch
	///
	/// WARNING! This is a non-deterministic call. Do not use this within
	/// consensus critical logic.
	fn current_time() -> u128 {
		std::time::SystemTime::now().duration_since(std::time::SystemTime::UNIX_EPOCH)
			.expect("Unix time doesn't go backwards; qed")
			.as_nanos()
	}

	/// Reset the trie database to the genesis state.
	fn wipe_db(&mut self) {
		self.wipe()
	}

	/// Commit pending storage changes to the trie database and clear the database cache.
	fn commit_db(&mut self) {
		self.commit()
	}

	/// Get the read/write count
	fn read_write_count(&self) -> (u32, u32, u32, u32) {
		self.read_write_count()
	}

	/// Reset the read/write count
	fn reset_read_write_count(&mut self) {
		self.reset_read_write_count()
	}

	fn set_whitelist(&mut self, new: Vec<Vec<u8>>) {
		self.set_whitelist(new)
	}
}

/// The pallet benchmarking trait.
pub trait Benchmarking<T> {
	/// Get the benchmarks available for this pallet. Generally there is one benchmark per
	/// extrinsic, so these are sometimes just called "extrinsics".
	fn benchmarks() -> Vec<&'static [u8]>;

	/// Run the benchmarks for this pallet.
	///
	/// Parameters
	/// - `name`: The name of extrinsic function or benchmark you want to benchmark encoded as
	///   bytes.
	/// - `steps`: The number of sample points you want to take across the range of parameters.
	/// - `lowest_range_values`: The lowest number for each range of parameters.
	/// - `highest_range_values`: The highest number for each range of parameters.
	/// - `repeat`: The number of times you want to repeat a benchmark.
	fn run_benchmark(
		name: &[u8],
		lowest_range_values: &[u32],
		highest_range_values: &[u32],
		steps: &[u32],
		repeat: u32,
		whitelist: &[Vec<u8>]
	) -> Result<Vec<T>, &'static str>;
}

/// The required setup for creating a benchmark.
pub trait BenchmarkingSetup<T> {
	/// Return the components and their ranges which should be tested in this benchmark.
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)>;

	/// Set up the storage, and prepare a closure to run the benchmark.
	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>;

	/// Set up the storage, and prepare a closure to test and verify the benchmark
	fn verify(&self, components: &[(BenchmarkParameter, u32)]) -> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>;
}

/// The required setup for creating a benchmark.
pub trait BenchmarkingSetupInstance<T, I> {
	/// Return the components and their ranges which should be tested in this benchmark.
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)>;

	/// Set up the storage, and prepare a closure to run the benchmark.
	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>;

	/// Set up the storage, and prepare a closure to test and verify the benchmark
	fn verify(&self, components: &[(BenchmarkParameter, u32)]) -> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>;
}

/// Grab an account, seeded by a name and index.
pub fn account<AccountId: Decode + Default>(name: &'static str, index: u32, seed: u32) -> AccountId {
	let entropy = (name, index, seed).using_encoded(blake2_256);
	AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}
