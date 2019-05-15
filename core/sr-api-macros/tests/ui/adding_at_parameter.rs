use client::decl_runtime_apis;

decl_runtime_apis! {
	pub trait Api {
		fn test(at: u64);
	}
}

fn main() {}
