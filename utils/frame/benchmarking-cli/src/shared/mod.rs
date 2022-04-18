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

use frame_support::weights::constants;

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

/// A Handlebars helper to add an underscore after every 3rd character,then format it,
/// i.e. a separator for large numbers : 123000000 -> 123_000 * WEIGHT_PER_NANOS .
#[derive(Clone, Copy)]
pub struct UnderscoreFormatHelper;

impl handlebars::HelperDef for UnderscoreFormatHelper {
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
		let underscore_format_param = underscore_format(param.value().render());
		out.write(&underscore_format_param)?;
		Ok(())
	}
}

/// Add an underscore after every 3rd character, then format it, i.e. a separator for large numbers: 123000000 -> 123_000 * WEIGHT_PER_NANOS .
fn underscore_format<Number>(i: Number) -> String
where
	Number: std::string::ToString,
{
	let mut s = String::new();
	let i_str = i.to_string();
	let f_u64 = i_str.parse::<f64>().unwrap();
	let j_str = (f_u64 / constants::WEIGHT_PER_NANOS as f64 ).to_string();
	let a = j_str.chars().rev().enumerate();
	for (idx, val) in a {
		if idx != 0 && idx % 3 == 0 {
			if val=='.' {
				
			}else{
				s.insert(0, '_');
			}
		}
		s.insert(0, val);
	}
	s.push_str(" * constants::WEIGHT_PER_NANOS ");
	s
}
