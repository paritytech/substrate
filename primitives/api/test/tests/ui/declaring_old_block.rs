use sp_runtime::traits::Block as BlockT;

sp_api::decl_runtime_apis! {
	pub trait Api<Block: BlockT> {
		fn test();
	}
}

fn main() {}
