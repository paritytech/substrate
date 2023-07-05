use sp_runtime::traits::Block as BlockT;
use substrate_test_runtime_client::runtime::Block;

struct Runtime {}

sp_api::decl_runtime_apis! {
	#[api_version(2)]
	pub trait Api {
		fn test1();
		fn test2();
		#[api_version(3)]
		fn test3();
	}
}

sp_api::impl_runtime_apis! {
	#[api_version(4)]
	impl self::Api<Block> for Runtime {
		fn test1() {}
		fn test2() {}
		fn test3() {}
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

fn main() {}
