#[macro_use]
extern crate substrate_client;
extern crate sr_primitives as runtime_primitives;
extern crate substrate_primitives as primitives;
#[macro_use]
extern crate parity_codec_derive;
extern crate serde;
extern crate core;

use primitives::hash::H256;
use runtime_primitives::traits::{
	BlakeTwo256, GetNodeBlockType, Extrinsic as ExtrinsicT, Block as BlockT
};
use runtime_primitives::generic::BlockId;
use substrate_client::runtime_api;
use primitives::AuthorityId;
use substrate_client::error::Result;

// All the stuff we need to declare our `Block`
pub type BlockNumber = u64;
pub type DigestItem = runtime_primitives::generic::DigestItem<H256, u64>;
pub type Digest = runtime_primitives::generic::Digest<DigestItem>;
#[derive(Clone, PartialEq, Eq, Encode, Decode, Debug)]
pub struct Extrinsic {}

impl serde::Serialize for Extrinsic {
	fn serialize<S>(
		&self,
		_: S
	) -> ::std::result::Result<S::Ok, S::Error> where S: ::serde::Serializer {
		unimplemented!()
	}
}
impl ExtrinsicT for Extrinsic {
	fn is_signed(&self) -> Option<bool> {
		unimplemented!()
	}
}
pub type Header = runtime_primitives::generic::Header<BlockNumber, BlakeTwo256, DigestItem>;
pub type Block = runtime_primitives::generic::Block<Header, Extrinsic>;

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
