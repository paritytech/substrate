use runtime_primitives::traits::Block as BlockT;
use client::decl_runtime_apis;

decl_runtime_apis! {
	pub trait Api<B: BlockT> {
		fn test();
	}
}

fn main() {}
