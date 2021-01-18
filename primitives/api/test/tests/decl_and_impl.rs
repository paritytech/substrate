// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use sp_api::{
	RuntimeApiInfo, decl_runtime_apis, impl_runtime_apis, mock_impl_runtime_apis,
	ApiError,
	ApiExt,
};
use sp_runtime::{traits::{GetNodeBlockType, Block as BlockT}, generic::BlockId};
use sp_core::NativeOrEncoded;
use substrate_test_runtime_client::runtime::Block;
use sp_blockchain::Result;

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
		fn wild_card(_: u32);
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

		fn wild_card(_: u32) {}
	}

	impl self::ApiWithCustomVersion<Block> for Runtime {
		fn same_name() {}
	}

	impl sp_api::Core<Block> for Runtime {
		fn version() -> sp_version::RuntimeVersion {
			unimplemented!()
		}
		fn execute_block(_: Block) {
			unimplemented!()
		}
		fn initialize_block(_: &<Block as BlockT>::Header) {
			unimplemented!()
		}
	}
}

struct MockApi {
	block: Option<Block>,
}

mock_impl_runtime_apis! {
	impl Api<Block> for MockApi {
		fn test(_: u64) {
			unimplemented!()
		}

		fn something_with_block(&self, _: Block) -> Block {
			self.block.clone().unwrap()
		}

		fn function_with_two_args(_: u64, _: Block) {
			unimplemented!()
		}

		#[advanced]
		fn same_name(_: &BlockId<Block>) ->
			std::result::Result<
				NativeOrEncoded<()>,
				ApiError
			>
		{
			Ok(().into())
		}

		#[advanced]
		fn wild_card(at: &BlockId<Block>, _: u32) ->
			std::result::Result<
				NativeOrEncoded<()>,
				ApiError
			>
		{
			if let BlockId::Number(1337) = at {
				// yeah
				Ok(().into())
			} else {
				Err(ApiError::new("MockApi", codec::Error::from("Ohh noooo")))
			}
		}
	}

	impl ApiWithCustomVersion<Block> for MockApi {
		fn same_name() {}
	}
}

type TestClient = substrate_test_runtime_client::client::Client<
	substrate_test_runtime_client::Backend,
	substrate_test_runtime_client::Executor,
	Block,
	RuntimeApi,
>;

#[test]
fn test_client_side_function_signature() {
	let _test: fn(&RuntimeApiImpl<Block, TestClient>, &BlockId<Block>, u64) -> Result<()> =
		RuntimeApiImpl::<Block, TestClient>::test;
	let _something_with_block:
		fn(&RuntimeApiImpl<Block, TestClient>, &BlockId<Block>, Block) -> Result<Block> =
			RuntimeApiImpl::<Block, TestClient>::something_with_block;

	#[allow(deprecated)]
	let _same_name_before_version_2:
		fn(&RuntimeApiImpl<Block, TestClient>, &BlockId<Block>) -> Result<String> =
			RuntimeApiImpl::<Block, TestClient>::same_name_before_version_2;
}

#[test]
fn check_runtime_api_info() {
	assert_eq!(&Api::<Block, Error = ()>::ID, &runtime_decl_for_Api::ID);
	assert_eq!(Api::<Block, Error = ()>::VERSION, runtime_decl_for_Api::VERSION);
	assert_eq!(Api::<Block, Error = ()>::VERSION, 1);

	assert_eq!(
		ApiWithCustomVersion::<Block, Error = ()>::VERSION,
		runtime_decl_for_ApiWithCustomVersion::VERSION,
	);
	assert_eq!(
		&ApiWithCustomVersion::<Block, Error = ()>::ID,
		&runtime_decl_for_ApiWithCustomVersion::ID,
	);
	assert_eq!(ApiWithCustomVersion::<Block, Error = ()>::VERSION, 2);
}

fn check_runtime_api_versions_contains<T: RuntimeApiInfo + ?Sized>() {
	assert!(RUNTIME_API_VERSIONS.iter().any(|v| v == &(T::ID, T::VERSION)));
}

#[test]
fn check_runtime_api_versions() {
	check_runtime_api_versions_contains::<dyn Api<Block, Error = ()>>();
	check_runtime_api_versions_contains::<dyn ApiWithCustomVersion<Block, Error = ()>>();
	check_runtime_api_versions_contains::<dyn sp_api::Core<Block, Error = ()>>();
}

#[test]
fn mock_runtime_api_has_api() {
	let mock = MockApi { block: None };

	assert!(
		mock.has_api::<dyn ApiWithCustomVersion<Block, Error = ()>>(&BlockId::Number(0)).unwrap(),
	);
	assert!(mock.has_api::<dyn Api<Block, Error = ()>>(&BlockId::Number(0)).unwrap());
}

#[test]
#[should_panic(expected = "Mocked runtime apis don't support calling deprecated api versions")]
fn mock_runtime_api_panics_on_calling_old_version() {
	let mock = MockApi { block: None };

	#[allow(deprecated)]
	let _ = mock.same_name_before_version_2(&BlockId::Number(0));
}

#[test]
fn mock_runtime_api_works_with_advanced() {
	let mock = MockApi { block: None };

	Api::<Block>::same_name(&mock, &BlockId::Number(0)).unwrap();
	mock.wild_card(&BlockId::Number(1337), 1).unwrap();
	assert_eq!(
		ApiError::new("MockApi", ::codec::Error::from("Ohh noooo")),
		mock.wild_card(&BlockId::Number(1336), 1).unwrap_err()
	);
}
