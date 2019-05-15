// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Compile fail tests.

mod changed_at_unknown_version {
	/*!
	```compile_fail
		#[macro_use]
		extern crate client;
		extern crate substrate_test_client as test_client;
		extern crate sr_primitives as runtime_primitives;
		extern crate substrate_primitives as primitives;

		use runtime_primitives::traits::GetNodeBlockType;
		use test_client::runtime::Block;

		/// The declaration of the `Runtime` type and the implementation of the `GetNodeBlockType`
		/// trait are done by the `construct_runtime!` macro in a real runtime.
		struct Runtime {}
		impl GetNodeBlockType for Runtime {
			type NodeBlock = Block;
		}

		decl_runtime_apis! {
			pub trait Api {
				#[changed_in(2)]
				fn test(data: u64);
				fn test(data: u64);
			}
		}

		fn main() {}
	```
	*/
}
