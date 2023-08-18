use sp_runtime_interface::runtime_interface;

#[runtime_interface]
trait Test {
	fn foo() {}

	#[cfg(feature = "bar-feature")]
	fn bar() {}

	#[cfg(not(feature = "bar-feature"))]
	fn qux() {}
}

fn main() {
	test::foo();
	test::bar();
	test::qux();
}
