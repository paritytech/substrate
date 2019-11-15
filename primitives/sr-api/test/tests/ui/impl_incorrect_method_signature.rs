use sr_primitives::traits::{GetNodeBlockType, Block as BlockT};
use test_client::runtime::Block;

/// The declaration of the `Runtime` type and the implementation of the `GetNodeBlockType`
/// trait are done by the `construct_runtime!` macro in a real runtime.
struct Runtime {}
impl GetNodeBlockType for Runtime {
	type NodeBlock = Block;
}

sr_api::decl_runtime_apis! {
	pub trait Api {
		fn test(data: u64);
	}
}

sr_api::impl_runtime_apis! {
	impl self::Api<Block> for Runtime {
		fn test(data: String) {}
	}

	impl sr_api::Core<Block> for Runtime {
		fn version() -> runtime_api::RuntimeVersion {
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

fn main() {}
