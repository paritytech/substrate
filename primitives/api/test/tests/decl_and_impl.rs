// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use sp_api::{
	RuntimeApiInfo, decl_runtime_apis, impl_runtime_apis, mock_impl_runtime_apis,
	ApiExt,
};

use sp_runtime::{traits::{GetNodeBlockType, Block as BlockT}, generic::BlockId};

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

		fn same_name() {}

		fn wild_card(_: u32) {}
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
