//! Set a nightly feature

extern crate rustc_version;
use rustc_version::{version, version_meta, Channel};

fn main() {
    // Assert we haven't travelled back in time
    assert!(version().unwrap().major >= 1);

    // Set cfg flags depending on release channel
    if let Channel::Nightly = version_meta().unwrap().channel {
        println!("cargo:rustc-cfg=feature=\"nightly\"");
    }
}
