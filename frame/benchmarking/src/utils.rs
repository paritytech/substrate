// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use codec::{Decode, Encode};
use frame_support::traits::StorageInfo;
use sp_io::hashing::blake2_256;
use sp_std::{prelude::Box, vec::Vec};
use sp_storage::TrackedStorageKey;

/// An alphabet of possible parameters to use for benchmarking.
#[derive(Encode, Decode, Clone, Copy, PartialEq, Debug)]
#[allow(missing_docs)]
#[allow(non_camel_case_types)]
pub enum BenchmarkParameter {
	a,
	b,
	c,
	d,
	e,
	f,
	g,
	h,
	i,
	j,
	k,
	l,
	m,
	n,
	o,
	p,
	q,
	r,
	s,
	t,
	u,
	v,
	w,
	x,
	y,
	z,
}

#[cfg(feature = "std")]
impl std::fmt::Display for BenchmarkParameter {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{:?}", self)
	}
}

/// The results of a single of benchmark.
#[derive(Encode, Decode, Clone, PartialEq, Debug)]
pub struct BenchmarkBatch {
	/// The pallet containing this benchmark.
	pub pallet: Vec<u8>,
	/// The instance of this pallet being benchmarked.
	pub instance: Vec<u8>,
	/// The extrinsic (or benchmark name) of this benchmark.
	pub benchmark: Vec<u8>,
	/// The results from this benchmark.
	pub results: Vec<BenchmarkResults>,
}

// TODO: could probably make API cleaner here.
/// The results of a single of benchmark, where time and db results are separated.
#[derive(Encode, Decode, Clone, PartialEq, Debug)]
pub struct BenchmarkBatchSplitResults {
	/// The pallet containing this benchmark.
	pub pallet: Vec<u8>,
	/// The instance of this pallet being benchmarked.
	pub instance: Vec<u8>,
	/// The extrinsic (or benchmark name) of this benchmark.
	pub benchmark: Vec<u8>,
	/// The extrinsic timing results from this benchmark.
	pub time_results: Vec<BenchmarkResults>,
	/// The db tracking results from this benchmark.
	pub db_results: Vec<BenchmarkResults>,
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
	pub proof_size: u32,
	pub keys: Vec<(Vec<u8>, u32, u32, bool)>,
}

/// Configuration used to setup and run runtime benchmarks.
#[derive(Encode, Decode, Default, Clone, PartialEq, Debug)]
pub struct BenchmarkConfig {
	/// The encoded name of the pallet to benchmark.
	pub pallet: Vec<u8>,
	/// The encoded name of the benchmark/extrinsic to run.
	pub benchmark: Vec<u8>,
	/// The selected component values to use when running the benchmark.
	pub selected_components: Vec<(BenchmarkParameter, u32)>,
	/// Enable an extra benchmark iteration which runs the verification logic for a benchmark.
	pub verify: bool,
	/// Number of times to repeat benchmark within the Wasm environment. (versus in the client)
	pub internal_repeats: u32,
}

/// A list of benchmarks available for a particular pallet and instance.
///
/// All `Vec<u8>` must be valid utf8 strings.
#[derive(Encode, Decode, Default, Clone, PartialEq, Debug)]
pub struct BenchmarkList {
	pub pallet: Vec<u8>,
	pub instance: Vec<u8>,
	pub benchmarks: Vec<BenchmarkMetadata>,
}

#[derive(Encode, Decode, Default, Clone, PartialEq, Debug)]
pub struct BenchmarkMetadata {
	pub name: Vec<u8>,
	pub components: Vec<(BenchmarkParameter, u32, u32)>,
}

sp_api::decl_runtime_apis! {
	/// Runtime api for benchmarking a FRAME runtime.
	pub trait Benchmark {
		/// Get the benchmark metadata available for this runtime.
		///
		/// Parameters
		/// - `extra`: Also list benchmarks marked "extra" which would otherwise not be
		///            needed for weight calculation.
		fn benchmark_metadata(extra: bool) -> (Vec<BenchmarkList>, Vec<StorageInfo>);

		/// Dispatch the given benchmark.
		fn dispatch_benchmark(config: BenchmarkConfig) -> Result<Vec<BenchmarkBatch>, sp_runtime::RuntimeString>;
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
		std::time::SystemTime::now()
			.duration_since(std::time::SystemTime::UNIX_EPOCH)
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

	/// Get the read/write count.
	fn read_write_count(&self) -> (u32, u32, u32, u32) {
		self.read_write_count()
	}

	/// Reset the read/write count.
	fn reset_read_write_count(&mut self) {
		self.reset_read_write_count()
	}

	/// Get the DB whitelist.
	fn get_whitelist(&self) -> Vec<TrackedStorageKey> {
		self.get_whitelist()
	}

	/// Set the DB whitelist.
	fn set_whitelist(&mut self, new: Vec<TrackedStorageKey>) {
		self.set_whitelist(new)
	}

	// Add a new item to the DB whitelist.
	fn add_to_whitelist(&mut self, add: TrackedStorageKey) {
		let mut whitelist = self.get_whitelist();
		match whitelist.iter_mut().find(|x| x.key == add.key) {
			// If we already have this key in the whitelist, update to be the most constrained value.
			Some(item) => {
				item.reads += add.reads;
				item.writes += add.writes;
				item.whitelisted = item.whitelisted || add.whitelisted;
			},
			// If the key does not exist, add it.
			None => {
				whitelist.push(add);
			},
		}
		self.set_whitelist(whitelist);
	}

	// Remove an item from the DB whitelist.
	fn remove_from_whitelist(&mut self, remove: Vec<u8>) {
		let mut whitelist = self.get_whitelist();
		whitelist.retain(|x| x.key != remove);
		self.set_whitelist(whitelist);
	}

	fn get_read_and_written_keys(&self) -> Vec<(Vec<u8>, u32, u32, bool)> {
		self.get_read_and_written_keys()
	}

	/// Get current estimated proof size.
	fn proof_size(&self) -> Option<u32> {
		self.proof_size()
	}
}

/// The pallet benchmarking trait.
pub trait Benchmarking<T> {
	/// Get the benchmarks available for this pallet. Generally there is one benchmark per
	/// extrinsic, so these are sometimes just called "extrinsics".
	///
	/// Parameters
	/// - `extra`: Also return benchmarks marked "extra" which would otherwise not be
	///            needed for weight calculation.
	fn benchmarks(extra: bool) -> Vec<BenchmarkMetadata>;

	/// Run the benchmarks for this pallet.
	fn run_benchmark(
		name: &[u8],
		selected_components: &[(BenchmarkParameter, u32)],
		whitelist: &[TrackedStorageKey],
		verify: bool,
		internal_repeats: u32,
	) -> Result<Vec<T>, &'static str>;
}

/// The required setup for creating a benchmark.
///
/// Instance generic parameter is optional and can be used in order to capture unused generics for
/// instantiable pallets.
pub trait BenchmarkingSetup<T, I = ()> {
	/// Return the components and their ranges which should be tested in this benchmark.
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)>;

	/// Set up the storage, and prepare a closure to run the benchmark.
	fn instance(
		&self,
		components: &[(BenchmarkParameter, u32)],
		verify: bool,
	) -> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>;
}

/// Grab an account, seeded by a name and index.
pub fn account<AccountId: Decode + Default>(
	name: &'static str,
	index: u32,
	seed: u32,
) -> AccountId {
	let entropy = (name, index, seed).using_encoded(blake2_256);
	AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

/// This caller account is automatically whitelisted for DB reads/writes by the benchmarking macro.
pub fn whitelisted_caller<AccountId: Decode + Default>() -> AccountId {
	account::<AccountId>("whitelisted_caller", 0, 0)
}

#[macro_export]
macro_rules! whitelist_account {
	($acc:ident) => {
		frame_benchmarking::benchmarking::add_to_whitelist(
			frame_system::Account::<T>::hashed_key_for(&$acc).into(),
		);
	};
}
