// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Support code to ease the process of generating bag thresholds.
//!
//! NOTE: this assume the runtime implements [`pallet_staking::Config`], as it requires an
//! implementation of the traits [`frame_support::traits::Currency`] and
//! [`frame_support::traits::CurrencyToVote`].
//!
//! The process of adding bags to a runtime requires only four steps.
//!
//! 1. Update the runtime definition.
//!
//!    ```ignore
//!    parameter_types!{
//!         pub const BagThresholds: &'static [u64] = &[];
//!    }
//!
//!    impl pallet_bags_list::Config for Runtime {
//!         // <snip>
//!         type BagThresholds = BagThresholds;
//!    }
//!    ```
//!
//! 2. Write a little program to generate the definitions. This program exists only to hook together
//! the runtime definitions with the various calculations here. Take a look at
//! _utils/frame/generate_bags/node-runtime_ for an example.
//!
//! 3. Run that program:
//!
//!    ```sh,notrust
//!    $ cargo run -p node-runtime-generate-bags -- --total-issuance 1234 --minimum-balance 1
//! output.rs    ```
//!
//! 4. Update the runtime definition.
//!
//!    ```diff,notrust
//!    + mod output;
//!    - pub const BagThresholds: &'static [u64] = &[];
//!    + pub const BagThresholds: &'static [u64] = &output::THRESHOLDS;
//!    ```

use frame_election_provider_support::VoteWeight;
use frame_support::traits::Get;
use std::{
	io::Write,
	path::{Path, PathBuf},
};

/// Compute the existential weight for the specified configuration.
///
/// Note that this value depends on the current issuance, a quantity known to change over time.
/// This makes the project of computing a static value suitable for inclusion in a static,
/// generated file _excitingly unstable_.
fn existential_weight<T: pallet_staking::Config>(
	total_issuance: u128,
	minimum_balance: u128,
) -> VoteWeight {
	use frame_support::traits::CurrencyToVote;

	T::CurrencyToVote::to_vote(
		minimum_balance
			.try_into()
			.map_err(|_| "failed to convert minimum_balance to type Balance")
			.unwrap(),
		total_issuance
			.try_into()
			.map_err(|_| "failed to convert total_issuance to type Balance")
			.unwrap(),
	)
}

/// Return the path to a header file used in this repository if is exists.
///
/// Just searches the git working directory root for files matching certain patterns; it's
/// pretty naive.
fn path_to_header_file() -> Option<PathBuf> {
	let mut workdir: &Path = &std::env::current_dir().ok()?;
	while !workdir.join(".git").exists() {
		workdir = workdir.parent()?;
	}

	for file_name in &["HEADER-APACHE2", "HEADER-GPL3", "HEADER", "file_header.txt"] {
		let path = workdir.join(file_name);
		if path.exists() {
			return Some(path)
		}
	}
	None
}

/// Create an underscore formatter: a formatter which inserts `_` every 3 digits of a number.
fn underscore_formatter() -> num_format::CustomFormat {
	num_format::CustomFormat::builder()
		.grouping(num_format::Grouping::Standard)
		.separator("_")
		.build()
		.expect("format described here meets all constraints")
}

/// Compute the constant ratio for the thresholds.
///
/// This ratio ensures that each bag, with the possible exceptions of certain small ones and the
/// final one, is a constant multiple of the previous, while fully occupying the `VoteWeight`
/// space.
pub fn constant_ratio(existential_weight: VoteWeight, n_bags: usize) -> f64 {
	((VoteWeight::MAX as f64 / existential_weight as f64).ln() / ((n_bags - 1) as f64)).exp()
}

/// Compute the list of bag thresholds.
///
/// Returns a list of exactly `n_bags` elements, except in the case of overflow.
/// The first element is always `existential_weight`.
/// The last element is always `VoteWeight::MAX`.
///
/// All other elements are computed from the previous according to the formula
/// `threshold[k + 1] = (threshold[k] * ratio).max(threshold[k] + 1);`
pub fn thresholds(
	existential_weight: VoteWeight,
	constant_ratio: f64,
	n_bags: usize,
) -> Vec<VoteWeight> {
	const WEIGHT_LIMIT: f64 = VoteWeight::MAX as f64;

	let mut thresholds = Vec::with_capacity(n_bags);

	if n_bags > 1 {
		thresholds.push(existential_weight);
	}

	while n_bags > 0 && thresholds.len() < n_bags - 1 {
		let last = thresholds.last().copied().unwrap_or(existential_weight);
		let successor = (last as f64 * constant_ratio).round().max(last as f64 + 1.0);
		if successor < WEIGHT_LIMIT {
			thresholds.push(successor as VoteWeight);
		} else {
			eprintln!("unexpectedly exceeded weight limit; breaking threshold generation loop");
			break
		}
	}

	thresholds.push(VoteWeight::MAX);

	debug_assert_eq!(thresholds.len(), n_bags);
	debug_assert!(n_bags == 0 || thresholds[0] == existential_weight);
	debug_assert!(n_bags == 0 || thresholds[thresholds.len() - 1] == VoteWeight::MAX);

	thresholds
}

/// Write a thresholds module to the path specified.
///
/// Parameters:
/// - `n_bags` the number of bags to generate.
/// - `output` the path to write to; should terminate with a Rust module name, i.e.
///   `foo/bar/thresholds.rs`.
/// - `total_issuance` the total amount of the currency in the network.
/// - `minimum_balance` the minimum balance of the currency required for an account to exist (i.e.
///   existential deposit).
///
/// This generated module contains, in order:
///
/// - The contents of the header file in this repository's root, if found.
/// - Module documentation noting that this is autogenerated and when.
/// - Some associated constants.
/// - The constant array of thresholds.
pub fn generate_thresholds<T: pallet_staking::Config>(
	n_bags: usize,
	output: &Path,
	total_issuance: u128,
	minimum_balance: u128,
) -> Result<(), std::io::Error> {
	// ensure the file is accessable
	if let Some(parent) = output.parent() {
		if !parent.exists() {
			std::fs::create_dir_all(parent)?;
		}
	}

	// copy the header file
	if let Some(header_path) = path_to_header_file() {
		std::fs::copy(header_path, output)?;
	}

	// open an append buffer
	let file = std::fs::OpenOptions::new().create(true).append(true).open(output)?;
	let mut buf = std::io::BufWriter::new(file);

	// create underscore formatter and format buffer
	let mut num_buf = num_format::Buffer::new();
	let format = underscore_formatter();

	// module docs
	let now = chrono::Utc::now();
	writeln!(buf)?;
	writeln!(buf, "//! Autogenerated bag thresholds.")?;
	writeln!(buf, "//!")?;
	writeln!(buf, "//! Generated on {}", now.to_rfc3339())?;
	writeln!(buf, "//! Arguments")?;
	writeln!(buf, "//! Total issuance: {}", &total_issuance)?;
	writeln!(buf, "//! Minimum balance: {}", &minimum_balance)?;

	writeln!(
		buf,
		"//! for the {} runtime.",
		<T as frame_system::Config>::Version::get().spec_name,
	)?;

	let existential_weight = existential_weight::<T>(total_issuance, minimum_balance);
	num_buf.write_formatted(&existential_weight, &format);
	writeln!(buf)?;
	writeln!(buf, "/// Existential weight for this runtime.")?;
	writeln!(buf, "#[cfg(any(test, feature = \"std\"))]")?;
	writeln!(buf, "#[allow(unused)]")?;
	writeln!(buf, "pub const EXISTENTIAL_WEIGHT: u64 = {};", num_buf.as_str())?;

	// constant ratio
	let constant_ratio = constant_ratio(existential_weight, n_bags);
	writeln!(buf)?;
	writeln!(buf, "/// Constant ratio between bags for this runtime.")?;
	writeln!(buf, "#[cfg(any(test, feature = \"std\"))]")?;
	writeln!(buf, "#[allow(unused)]")?;
	writeln!(buf, "pub const CONSTANT_RATIO: f64 = {:.16};", constant_ratio)?;

	// thresholds
	let thresholds = thresholds(existential_weight, constant_ratio, n_bags);
	writeln!(buf)?;
	writeln!(buf, "/// Upper thresholds delimiting the bag list.")?;
	writeln!(buf, "pub const THRESHOLDS: [u64; {}] = [", thresholds.len())?;
	for threshold in &thresholds {
		num_buf.write_formatted(threshold, &format);
		// u64::MAX, with spacers every 3 digits, is 26 characters wide
		writeln!(buf, "	{:>26},", num_buf.as_str())?;
	}
	writeln!(buf, "];")?;

	// thresholds balance
	writeln!(buf)?;
	writeln!(buf, "/// Upper thresholds delimiting the bag list.")?;
	writeln!(buf, "pub const THRESHOLDS_BALANCES: [u128; {}] = [", thresholds.len())?;
	for threshold in thresholds {
		num_buf.write_formatted(&threshold, &format);
		// u64::MAX, with spacers every 3 digits, is 26 characters wide
		writeln!(buf, "	{:>26},", num_buf.as_str())?;
	}
	writeln!(buf, "];")?;

	Ok(())
}
