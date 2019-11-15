use sr_primitives::traits::Block as BlockT;

sr_api::decl_runtime_apis! {
	pub trait Api<Block: BlockT> {
		fn test();
	}
}

fn main() {}
