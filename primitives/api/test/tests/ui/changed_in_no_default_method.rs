use sp_runtime::traits::GetNodeBlockType;
use substrate_test_runtime_client::runtime::Block;

/// The declaration of the `Runtime` type and the implementation of the `GetNodeBlockType`
/// trait are done by the `construct_runtime!` macro in a real runtime.
struct Runtime {}
impl GetNodeBlockType for Runtime {
	type NodeBlock = Block;
}

sp_api::decl_runtime_apis! {
	#[api_version(2)]
	pub trait Api {
		#[changed_in(2)]
		fn test(data: u64);
	}
}

fn main() {}
