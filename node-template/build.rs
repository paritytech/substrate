use std::{env, path::PathBuf};

use vergen::{ConstantsFlags, generate_cargo_keys};

const ERROR_MSG: &str = "Failed to generate metadata files";

fn main() {
	generate_cargo_keys(ConstantsFlags::SHA_SHORT).expect(ERROR_MSG);

	let mut manifest_dir = PathBuf::from(
		env::var("CARGO_MANIFEST_DIR").expect("`CARGO_MANIFEST_DIR` is always set by cargo.")
	);

	while manifest_dir.parent().is_some() {
		if manifest_dir.join(".git/HEAD").exists() {
			println!("cargo:rerun-if-changed={}", manifest_dir.join(".git/HEAD").display());
			return
		}

		manifest_dir.pop();
	}

	println!("cargo:warning=Could not find `.git/HEAD` from manifest dir!");
}
