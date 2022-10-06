#[cfg(feature = "build-docs")]
use std::process::Command;

#[cfg(not(feature = "build-docs"))]
fn main() {}

#[cfg(feature = "build-docs")]
fn main() {
	println!("cargo:rerun-if-changed=src/lib.rs");
	let _ = Command::new("cargo").arg("readme").arg(">").arg("README.md").output().unwrap();
}
