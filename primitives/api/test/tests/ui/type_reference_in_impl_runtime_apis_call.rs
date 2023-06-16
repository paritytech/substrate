use sp_runtime::traits::Block as BlockT;
use substrate_test_runtime_client::runtime::Block;

/// The declaration of the `Runtime` type is done by the `construct_runtime!` macro in a real
/// runtime.
struct Runtime {}

sp_api::decl_runtime_apis! {
	pub trait Api {
		fn test(data: u64);
	}
}

sp_api::impl_runtime_apis! {
	impl self::Api<Block> for Runtime {
		fn test(data: &u64) {
			unimplemented!()
		}
	}

	impl sp_api::Core<Block> for Runtime {
		fn version() -> sp_api::RuntimeVersion {
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
