use std::env;

#[test]
fn ui() {
	// As trybuild is using `cargo check`, we don't need the real WASM binaries.
	env::set_var("BUILD_DUMMY_WASM_BINARY", "1");

	let t = trybuild::TestCases::new();
	t.compile_fail("tests/construct_runtime_ui/*.rs");
}
