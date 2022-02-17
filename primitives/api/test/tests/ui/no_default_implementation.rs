sp_api::decl_runtime_apis! {
	pub trait Api {
		fn test() {
			println!("Hey, I'm a default implementation!");
		}
	}
}

fn main() {}
