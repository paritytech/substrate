/// The declaration of the `Runtime` type is done by the `construct_runtime!` macro in a real
/// runtime.
struct Runtime {}

sp_api::decl_runtime_apis! {
	#[api_version(2)]
	pub trait Api {
		#[changed_in(2)]
		fn test(data: u64);
	}
}

fn main() {}
