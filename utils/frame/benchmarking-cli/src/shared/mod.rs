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

//! Code that is shared among all benchmarking sub-commands.

pub mod record;
pub mod stats;
pub mod weight_params;

pub use record::BenchRecord;
pub use stats::{StatSelect, Stats};
pub use weight_params::WeightParams;

use rand::prelude::*;

/// A Handlebars helper to add an underscore after every 3rd character,
/// i.e. a separator for large numbers.
#[derive(Clone, Copy)]
pub struct UnderscoreHelper;

impl handlebars::HelperDef for UnderscoreHelper {
	fn call<'reg: 'rc, 'rc>(
		&self,
		h: &handlebars::Helper,
		_: &handlebars::Handlebars,
		_: &handlebars::Context,
		_rc: &mut handlebars::RenderContext,
		out: &mut dyn handlebars::Output,
	) -> handlebars::HelperResult {
		use handlebars::JsonRender;
		let param = h.param(0).unwrap();
		let underscore_param = underscore(param.value().render());
		out.write(&underscore_param)?;
		Ok(())
	}
}

/// Add an underscore after every 3rd character, i.e. a separator for large numbers.
fn underscore<Number>(i: Number) -> String
where
	Number: std::string::ToString,
{
	let mut s = String::new();
	let i_str = i.to_string();
	let a = i_str.chars().rev().enumerate();
	for (idx, val) in a {
		if idx != 0 && idx % 3 == 0 {
			s.insert(0, '_');
		}
		s.insert(0, val);
	}
	s
}

/// Returns an rng and the seed that was used to create it.
///
/// Uses a random seed if none is provided.
pub fn new_rng(seed: Option<u64>) -> (impl rand::Rng, u64) {
	let seed = seed.unwrap_or(rand::thread_rng().gen::<u64>());
	(rand_pcg::Pcg64::seed_from_u64(seed), seed)
}

/// Returns an error if a debug profile is detected.
///
/// The rust compiler only exposes the binary information whether
/// or not we are in a `debug` build.
/// This means that `release` and `production` cannot be told apart.
/// This function additionally checks for OPT-LEVEL = 3.
pub fn check_build_profile() -> Result<(), String> {
	if cfg!(build_profile = "debug") {
		Err("Detected a `debug` profile".into())
	} else if !cfg!(build_opt_level = "3") {
		Err("The optimization level is not set to 3".into())
	} else {
		Ok(())
	}
}
