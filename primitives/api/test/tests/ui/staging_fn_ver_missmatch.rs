/// The declaration of the `Runtime` type is done by the `construct_runtime!` macro in a real
/// runtime.
struct Runtime {}

sp_api::decl_runtime_apis! {
	pub trait Api1 {
		fn test(data: u64);
		#[api_version(99)]
		fn staging();
	}
}

sp_api::impl_runtime_apis! {
	#[cfg_attr(feature = "enable-staging-api", api_version(42))]
	impl self::Api1<Block> for Runtime {
		fn test(data: u64) {
			unimplemented!()
		}

		#[cfg_attr(feature = "enable-staging-api", api_version(99))]
		fn staging(data: u64) {
			unimplemented!()
		}
	}
}

fn main() {}
