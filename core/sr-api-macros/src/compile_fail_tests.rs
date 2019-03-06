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

mod declaring_own_block {
	/*!
	```compile_fail
		#[macro_use]
		extern crate client;
		extern crate sr_primitives as runtime_primitives;

		use runtime_primitives::traits::Block as BlockT;

		decl_runtime_apis! {
			pub trait Api<Block: BlockT> {
				fn test();
			}
		}

		fn main() {}
	```
	*/
}

mod declaring_own_block_with_different_name {
	/*!
	```compile_fail
		#[macro_use]
		extern crate client;
		extern crate sr_primitives as runtime_primitives;

		use runtime_primitives::traits::Block as BlockT;

		decl_runtime_apis! {
			pub trait Api<B: BlockT> {
				fn test();
			}
		}

		fn main() {}
	```
	*/
}

mod adding_self_parameter {
	/*!
	```compile_fail
		#[macro_use]
		extern crate client;
		extern crate sr_primitives as runtime_primitives;

		decl_runtime_apis! {
			pub trait Api {
				fn test(&self);
			}
		}

		fn main() {}
	```
	*/
}

mod adding_at_parameter {
	/*!
	```compile_fail
		#[macro_use]
		extern crate client;
		extern crate sr_primitives as runtime_primitives;

		decl_runtime_apis! {
			pub trait Api {
				fn test(at: u64);
			}
		}

		fn main() {}
	```
	*/
}

mod invalid_api_version {
	/*!
	```compile_fail
		#[macro_use]
		extern crate client;
		extern crate sr_primitives as runtime_primitives;

		decl_runtime_apis! {
			#[api_version]
			pub trait Api {
				fn test(data: u64);
			}
		}

		fn main() {}
	```
	*/
}

mod invalid_api_version_2 {
	/*!
	```compile_fail
		#[macro_use]
		extern crate client;
		extern crate sr_primitives as runtime_primitives;

		decl_runtime_apis! {
			#[api_version("1")]
			pub trait Api {
				fn test(data: u64);
			}
		}

		fn main() {}
	```
	*/
}

mod invalid_api_version_3 {
	/*!
	```compile_fail
		#[macro_use]
		extern crate client;
		extern crate sr_primitives as runtime_primitives;

		decl_runtime_apis! {
			#[api_version()]
			pub trait Api {
				fn test(data: u64);
			}
		}

		fn main() {}
	```
	*/
}

mod missing_block_generic_parameter {
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
				fn test(data: u64);
			}
		}

		impl_runtime_apis! {
			impl self::Api for Runtime {
				fn test(data: u64) {
					unimplemented!()
				}
			}
		}

		fn main() {}
	```
	*/
}

mod missing_path_for_trait {
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
				fn test(data: u64);
			}
		}

		impl_runtime_apis! {
			impl Api<Block> for Runtime {
				fn test(data: u64) {
					unimplemented!()
				}
			}
		}

		fn main() {}
	```
	*/
}

mod empty_impl_runtime_apis_call {
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
				fn test(data: u64);
			}
		}

		impl_runtime_apis! {}

		fn main() {}
	```
	*/
}

mod type_reference_in_impl_runtime_apis_call {
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
				fn test(data: u64);
			}
		}

		impl_runtime_apis! {
			impl self::Api<Block> for Runtime {
				fn test(data: &u64) {
					unimplemented!()
				}
			}
		}

		fn main() {}
	```
	*/
}

mod impl_incorrect_method_signature {
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
				fn test(data: u64);
			}
		}

		impl_runtime_apis! {
			impl self::Api<Block> for Runtime {
				fn test(data: String) {}
			}
		}

		fn main() {}
	```
	*/
}

mod impl_two_traits_with_same_name {
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
				fn test(data: u64);
			}
		}

		mod second {
			decl_runtime_apis! {
				pub trait Api {
					fn test2(data: u64);
				}
			}
		}

		impl_runtime_apis! {
			impl self::Api<Block> for Runtime {
				fn test(data: u64) {}
			}

			impl second::Api<Block> for Runtime {
				fn test2(data: u64) {}
			}
		}

		fn main() {}
	```
	*/
}

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
