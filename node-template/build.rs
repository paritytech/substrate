use vergen::{ConstantsFlags, generate_cargo_keys};

const ERROR_MSG: &str = "Failed to generate metadata files";

fn main() {
	generate_cargo_keys(ConstantsFlags::all()).expect(ERROR_MSG);
	println!("cargo:rerun-if-changed=.git/HEAD");
}
