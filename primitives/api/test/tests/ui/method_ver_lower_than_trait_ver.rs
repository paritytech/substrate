sp_api::decl_runtime_apis! {
	#[api_version(2)]
	pub trait Api {
		#[api_version(1)]
		fn test(data: u64);
	}
}

fn main() {}