// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
