#[macro_use]
extern crate client;
extern crate sr_primitives as runtime_primitives;

use runtime_primitives::traits::Block as BlockT;

decl_runtime_apis! {
	pub trait Api<Block: BlockT> {
		fn test();
	}
}

fn main() {}
