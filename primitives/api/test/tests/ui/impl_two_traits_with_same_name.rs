/// The declaration of the `Runtime` type  is done by the `construct_runtime!` macro in a real
/// runtime.
struct Runtime {}

sp_api::decl_runtime_apis! {
	pub trait Api {
		fn test(data: u64);
	}
}

mod second {
	sp_api::decl_runtime_apis! {
		pub trait Api {
			fn test2(data: u64);
		}
	}
}

sp_api::impl_runtime_apis! {
	impl self::Api<Block> for Runtime {
		fn test(data: u64) {}
	}

	impl second::Api<Block> for Runtime {
		fn test2(data: u64) {}
	}
}

fn main() {}
