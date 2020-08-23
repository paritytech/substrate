sp_api::decl_runtime_apis! {
	pub trait Api<B: BlockT> {
		fn test();
	}
}

fn main() {}
