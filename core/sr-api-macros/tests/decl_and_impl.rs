// Copyright 2019 Parity Technologies (UK) Ltd.
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

use runtime_primitives::traits::{GetNodeBlockType, Block as BlockT, AuthorityIdFor};
use runtime_primitives::generic::BlockId;
use client::runtime_api::{self, RuntimeApiInfo};
use client::{error::Result, decl_runtime_apis, impl_runtime_apis};
use test_client::runtime::Block;

/// The declaration of the `Runtime` type and the implementation of the `GetNodeBlockType`
/// trait are done by the `construct_runtime!` macro in a real runtime.
pub struct Runtime {}
impl GetNodeBlockType for Runtime {
	type NodeBlock = Block;
}

decl_runtime_apis! {
	pub trait Api {
		fn test(data: u64);
		fn something_with_block(block: Block) -> Block;
		fn function_with_two_args(data: u64, block: Block);
		fn same_name();
	}

	#[api_version(2)]
	pub trait ApiWithCustomVersion {
		fn same_name();
		#[changed_in(2)]
		fn same_name() -> String;
	}
}

impl_runtime_apis! {
	impl self::Api<Block> for Runtime {
		fn test(_: u64) {
			unimplemented!()
		}

		fn something_with_block(_: Block) -> Block {
			unimplemented!()
		}

		fn function_with_two_args(_: u64, _: Block) {
			unimplemented!()
		}

		fn same_name() {}
	}

	impl self::ApiWithCustomVersion<Block> for Runtime {
		fn same_name() {}
	}

	impl runtime_api::Core<Block> for Runtime {
		fn version() -> runtime_api::RuntimeVersion {
			unimplemented!()
		}
		fn execute_block(_: Block) {
			unimplemented!()
		}
		fn initialize_block(_: &<Block as BlockT>::Header) {
			unimplemented!()
		}
		fn authorities() -> Vec<AuthorityIdFor<Block>> {
			unimplemented!()
		}
	}
}

type TestClient = client::Client<test_client::Backend, test_client::Executor, Block, RuntimeApi>;

#[test]
fn test_client_side_function_signature() {
	let _test: fn(&RuntimeApiImpl<TestClient>, &BlockId<Block>, u64) -> Result<()> =
		RuntimeApiImpl::<TestClient>::test;
	let _something_with_block:
		fn(&RuntimeApiImpl<TestClient>, &BlockId<Block>, Block) -> Result<Block> =
			RuntimeApiImpl::<TestClient>::something_with_block;

	#[allow(deprecated)]
	let _same_name_before_version_2:
		fn(&RuntimeApiImpl<TestClient>, &BlockId<Block>) -> Result<String> =
			RuntimeApiImpl::<TestClient>::same_name_before_version_2;
}

#[test]
fn test_runtime_side_function_signature() {
	let _api_same_name: fn(input_data: *mut u8, input_len: usize) -> u64 = api::Api_same_name;
	let _api_with_version_same_name: fn(input_data: *mut u8, input_len: usize) -> u64 =
		api::ApiWithCustomVersion_same_name;
}

#[test]
fn check_runtime_api_info() {
	assert_eq!(&Api::<Block>::ID, &runtime_decl_for_Api::ID);
	assert_eq!(Api::<Block>::VERSION, runtime_decl_for_Api::VERSION);
	assert_eq!(Api::<Block>::VERSION, 1);

	assert_eq!(
		ApiWithCustomVersion::<Block>::VERSION, runtime_decl_for_ApiWithCustomVersion::VERSION
	);
	assert_eq!(&ApiWithCustomVersion::<Block>::ID, &runtime_decl_for_ApiWithCustomVersion::ID);
	assert_eq!(ApiWithCustomVersion::<Block>::VERSION, 2);
}

fn check_runtime_api_versions_contains<T: RuntimeApiInfo + ?Sized>() {
	assert!(RUNTIME_API_VERSIONS.iter().any(|v| v == &(T::ID, T::VERSION)));
}

#[test]
fn check_runtime_api_versions() {
	check_runtime_api_versions_contains::<Api<Block>>();
	check_runtime_api_versions_contains::<ApiWithCustomVersion<Block>>();
	check_runtime_api_versions_contains::<runtime_api::Core<Block>>();
}
