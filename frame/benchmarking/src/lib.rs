// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Interfaces and types for benchmarking a FRAME runtime.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::vec::Vec;

/// An alphabet of possible parameters to use for benchmarking.
#[derive(codec::Encode, codec::Decode, Clone, Copy, PartialEq, Debug)]
#[allow(missing_docs)]
pub enum BenchmarkParameter {
	A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z,
}

/// Results from running benchmarks on a FRAME pallet.
/// Contains duration of the function call in nanoseconds along with the benchmark parameters
/// used for that benchmark result.
pub type BenchmarkResults = (Vec<(BenchmarkParameter, u32)>, u128);

sp_api::decl_runtime_apis! {
	/// Runtime api for benchmarking a FRAME runtime.
	pub trait Benchmark {
		/// Dispatch the given benchmark.
		fn dispatch_benchmark(
			module: Vec<u8>,
			extrinsic: Vec<u8>,
			steps: u32,
			repeat: u32,
		) -> Option<Vec<BenchmarkResults>>;
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
}

/// The pallet benchmarking trait.
pub trait Benchmarking<T> {
	/// Run the benchmarks for this pallet.
	///
	/// Parameters
	/// - `extrinsic`: The name of extrinsic function you want to benchmark encoded as bytes.
	/// - `steps`: The number of sample points you want to take across the range of parameters.
	/// - `repeat`: The number of times you want to repeat a benchmark.
	fn run_benchmark(extrinsic: Vec<u8>, steps: u32, repeat: u32) -> Result<Vec<T>, &'static str>;
}

/// The required setup for creating a benchmark.
pub trait BenchmarkingSetup<T, Call, RawOrigin> {
	/// Return the components and their ranges which should be tested in this benchmark.
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)>;

	/// Set up the storage, and prepare a call and caller to test in a single run of the benchmark.
	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> Result<(Call, RawOrigin), &'static str>;
}

/// Creates a `SelectedBenchmark` enum implementing `BenchmarkingSetup`.
///
/// Every variant must implement [`BenchmarkingSetup`].
///
/// ```nocompile
///
/// struct Transfer;
/// impl BenchmarkingSetup for Transfer { ... }
///
/// struct SetBalance;
/// impl BenchmarkingSetup for SetBalance { ... }
///
/// selected_benchmark!(Transfer, SetBalance);
/// ```
#[macro_export]
macro_rules! selected_benchmark {
	(
		$( $bench:ident ),*
	) => {
		// The list of available benchmarks for this pallet.
		enum SelectedBenchmark {
			$( $bench, )*
		}

		// Allow us to select a benchmark from the list of available benchmarks.
		impl<T: Trait> $crate::BenchmarkingSetup<T, Call<T>, RawOrigin<T::AccountId>> for SelectedBenchmark {
			fn components(&self) -> Vec<($crate::BenchmarkParameter, u32, u32)> {
				match self {
					$( Self::$bench => <$bench as $crate::BenchmarkingSetup<
						T,
						Call<T>,
						RawOrigin<T::AccountId>,
					>>::components(&$bench), )*
				}
			}

			fn instance(&self, components: &[($crate::BenchmarkParameter, u32)])
				-> Result<(Call<T>, RawOrigin<T::AccountId>), &'static str>
			{
				match self {
					$( Self::$bench => <$bench as $crate::BenchmarkingSetup<
						T,
						Call<T>,
						RawOrigin<T::AccountId>,
					>>::instance(&$bench, components), )*
				}
			}
		}
	};
}
