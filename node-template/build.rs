use vergen::{generate_cargo_keys, ConstantsFlags};

const ERROR_MSG: &str = "Failed to generate metadata files";

fn main() {
    generate_cargo_keys(ConstantsFlags::all()).expect(ERROR_MSG);
    println!("cargo:rerun-if-changed=.git/HEAD");
}
