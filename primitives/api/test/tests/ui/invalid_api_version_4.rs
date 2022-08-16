sp_api::decl_runtime_apis! {
	pub trait Api {
		#[api_version("1")]
		fn test(data: u64);
	}
}

fn main() {}
