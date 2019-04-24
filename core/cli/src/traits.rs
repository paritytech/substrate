// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
use structopt::{StructOpt, clap::App};

/// Something that can augment a clapp app with further parameters.
/// `derive(StructOpt)` is implementing this function by default, so a macro `impl_augment_clap!`
/// is provided to simplify the implementation of this trait.
pub trait AugmentClap: StructOpt {
	/// Augment the given clap `App` with further parameters.
	fn augment_clap<'a, 'b>(app: App<'a, 'b>) -> App<'a, 'b>;
}

/// Macro for implementing the `AugmentClap` trait.
/// This requires that the given type uses `derive(StructOpt)`!
#[macro_export]
macro_rules! impl_augment_clap {
	( $type:ident ) => {
		impl $crate::AugmentClap for $type {
			fn augment_clap<'a, 'b>(app: $crate::App<'a, 'b>) -> $crate::App<'a, 'b> {
				$type::augment_clap(app)
			}
		}
	}
}

/// Returns the log filter given by the user as commandline argument.
pub trait GetLogFilter {
	/// Returns the set log filter.
	fn get_log_filter(&self) -> Option<String>;
}
