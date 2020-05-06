use substrate_test_runtime_client::runtime::Block;

struct Block2;

sp_api::decl_runtime_apis! {
	pub trait Api {
		fn test(data: u64);
	}

	pub trait Api2 {
		fn test(data: u64);
	}
}

struct MockApi;

sp_api::mock_impl_runtime_apis! {
	impl Api<Block> for MockApi {
		fn test(data: u64) {}
	}

	impl Api2<Block2> for MockApi {
		fn test(data: u64) {}
	}
}

fn main() {}
