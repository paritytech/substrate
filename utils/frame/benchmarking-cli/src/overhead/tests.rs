// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Test that the weight template is renders correctly.

#![cfg(test)]

use super::template::TemplateData;
use crate::{
	extrinsic::bench::{BlockProofSize, ProofSize},
	overhead::cmd::{BenchmarkType, OverheadParams},
	shared::{Stats, WeightParams},
};

/// Test that the following constants are present in the output:
/// - `ExtrinsicBaseRefTime`
/// - `ExtrinsicBaseWeight`
#[test]
fn template_render_extrinsic_works() {
	let (params, time, _) = setup();
	let render = TemplateData::new(BenchmarkType::Extrinsic, "", &params, time, None)
		.unwrap()
		.render()
		.unwrap();

	let want =
		"pub const ExtrinsicBaseRefTime: u64 = WEIGHT_PER_NANOS.ref_time().saturating_mul(3_000);";
	assert_contains(&render, want);
}

/// Test that the following constants are present in the output:
/// - `BlockExecutionRefTime`
/// - `EmptyBlockProofSize`
/// - `NonEmptyBlockProofSize`
/// - `BlockExecutionWeight`
#[test]
fn template_render_block_works() {
	let (params, time, proof) = setup();

	let render = TemplateData::new(BenchmarkType::Block, "", &params, time, Some(proof))
		.unwrap()
		.render()
		.unwrap();

	let want =
		"pub const BlockExecutionRefTime: u64 = WEIGHT_PER_NANOS.ref_time().saturating_mul(3_000);";
	assert_contains(&render, want);
	let want = "pub const EmptyBlockProofSize: u64 = 4_096";
	assert_contains(&render, want);
	let want = "pub const NonEmptyBlockProofSize: u64 = 8_192";
	assert_contains(&render, want);
	let want = "pub const BlockExecutionWeight: Weight = Weight::from_parts(BlockExecutionRefTime::get(),NonEmptyBlockProofSize::get(),);";
	assert_contains(&render, want);
}

/// Checks that the nightly *rustfmt* does not change the rendered template output.
///
/// Is only run when `BENCHMARK_OVERHEAD_RUSTFMT` is defined.
/// Requires `rustup` and nightly `rustfmt` to be installed.
#[test]
fn template_rustfmt_works() {
	if std::env::var("BENCHMARK_OVERHEAD_RUSTFMT").is_err() {
		return
	}

	// Extrinsic weights are rendered in a correctly formatted matter.
	{
		let (params, time, _) = setup();
		let render = TemplateData::new(BenchmarkType::Extrinsic, "", &params, time, None)
			.unwrap()
			.render()
			.unwrap();
		assert_is_rustfmt_formatted(&render);
	}
	// Block weights are rendered in a correctly formatted matter.
	{
		let (params, time, proof) = setup();
		let render = TemplateData::new(BenchmarkType::Block, "", &params, time, Some(proof))
			.unwrap()
			.render()
			.unwrap();
		assert_is_rustfmt_formatted(&render);
	}
}

/// Setup for the tests.
fn setup() -> (OverheadParams, Stats, BlockProofSize) {
	let params = OverheadParams {
		weight: WeightParams {
			weight_mul: 1., // calc_ref_time panics otherwise
			..Default::default()
		},
		..Default::default()
	};
	let time_record = vec![1000u64, 2000, 3000, 4000, 5000];
	let time = Stats::new(&time_record).unwrap();
	let empty = ProofSize { storage: 4 * 1024, ..Default::default() };
	let non_empty = ProofSize { storage: 8 * 1024, ..Default::default() };

	(params, time, BlockProofSize { empty, non_empty })
}

/// Asserts that `got` contains `want`.
fn assert_contains(got: &str, want: &str) {
	if !got
		.chars()
		.filter(|c| c != &'\n' && c != &'\t')
		.collect::<String>()
		.contains(want)
	{
		panic!("Filled template is missing string. Template:\n{}\nExpected:\n{}", got, want);
	}
}

/// Asserts that the given string is formatted correctly according to nightly `rustfmt`.
///
/// This requires nightly `rustfmt` and `rustup` to be installed. It assumes to find a
/// `rustfmt` config file at the root of the workspace.
fn assert_is_rustfmt_formatted(code: &str) {
	use std::io::Write;
	let mut cmd = std::process::Command::new("rustup");
	cmd.arg("run")
		.arg("nightly")
		.arg("rustfmt")
		.arg("--config-path")
		.arg("../../../rustfmt.toml") // Use the Substrate rustfmt config.
		.arg("--check")
		.arg("-q");

	let mut child = cmd
		.stdin(std::process::Stdio::piped())
		.stdout(std::process::Stdio::piped())
		.spawn()
		.unwrap();
	child.stdin.as_mut().unwrap().write_all(code.as_bytes()).unwrap();

	let output = child.wait_with_output().unwrap();
	assert!(output.status.success());
	assert_eq!(String::from_utf8(output.stdout).unwrap(), "", "rustfmt diff must be empty");
}
