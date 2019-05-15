use runtime_primitives::traits::GetNodeBlockType;
use test_client::runtime::Block;
use client::decl_runtime_apis;

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
