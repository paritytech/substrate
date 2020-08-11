use substrate_test_runtime_client::runtime::Block;

sp_api::decl_runtime_apis! {
	pub trait Api {
		fn test(data: u64);
	}
}

struct MockApi;

sp_api::mock_impl_runtime_apis! {
	impl Api<Block> for MockApi {
		type OtherData = u32;

		fn test(data: u64) {}
	}
}

fn main() {}
