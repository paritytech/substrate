#[test]
fn tests() {
	let t = trybuild::TestCases::new();
	t.compile_fail("tests/ui/substrate_cli/unknown_attrs.rs");
	t.compile_fail("tests/ui/substrate_cli/missing_sha_short.rs");
}
