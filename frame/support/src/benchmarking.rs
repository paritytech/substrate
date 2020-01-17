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

// #[doc(hidden)]
// #[allow(deprecated)]
// pub use crate::sp_runtime::traits::Benchmarking;

pub trait Benchmarking {
	type Call;
	fn get_call(module: &str, function: &str) -> Self::Call;
}

pub trait Other {
	type Potato;
	fn get_call(module: &str, function: &str) -> Self::Potato;
}


// #[macro_export]
// macro_rules! impl_outer_benchmarking {
// 	(
// 		impl Benchmarking for $runtime:ident {
// 			$( $module:ident )*
// 		}
// 	) => {
// 		#[allow(deprecated)]
// 		impl $crate::benchmarking::Benchmarking for $runtime {
// 			type Call = Call;

// 			fn make_call() -> Self::Call {
// 				#[cfg(feature = "std")]
// 				println!("module: {:?}", stringify!( $( $module::metadata(), )* ))
// 			}
// 		}
// 	};
// }
