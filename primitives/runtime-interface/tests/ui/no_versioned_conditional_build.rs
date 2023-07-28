use sp_runtime_interface::runtime_interface;

#[runtime_interface]
trait Test {
	fn foo() {}

	#[version(2)]
	#[cfg(feature = "foo-feature")]
	fn foo() {}
}

fn main() {}
