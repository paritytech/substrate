#[macro_use]
extern crate substrate_client;
extern crate sr_primitives as runtime_primitives;
extern crate substrate_primitives as primitives;
extern crate substrate_test_client as test_client;

use runtime_primitives::traits::{GetNodeBlockType, Block as BlockT};
use runtime_primitives::generic::BlockId;
use primitives::AuthorityId;
use substrate_client::runtime_api::{self, RuntimeApiInfo};
use substrate_client::error::Result;
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
	}

	#[api_version(2)]
	pub trait ApiWithCustomVersion {}
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
	}

	impl self::ApiWithCustomVersion<Block> for Runtime {}

	impl runtime_api::Core<Block> for Runtime {
		fn version() -> runtime_api::RuntimeVersion {
			unimplemented!()
		}
		fn authorities() -> Vec<AuthorityId> {
			unimplemented!()
		}
		fn execute_block(_: Block) {
			unimplemented!()
		}
		fn initialise_block(_: <Block as BlockT>::Header) {
			unimplemented!()
		}
	}
}

#[test]
fn test_client_side_function_signature() {
	let _test: fn(&RuntimeApi, &BlockId<Block>, &u64) -> Result<()>  = RuntimeApi::test;
	let _something_with_block: fn(&RuntimeApi, &BlockId<Block>, &Block) -> Result<Block> =
		RuntimeApi::something_with_block;
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
