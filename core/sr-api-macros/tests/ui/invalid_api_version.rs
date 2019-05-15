use client::decl_runtime_apis;

decl_runtime_apis! {
	#[api_version]
	pub trait Api {
		fn test(data: u64);
	}
}

fn main() {}
