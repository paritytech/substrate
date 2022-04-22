use std::env;

/// Exposes the optimization level as `opt_level` to the rust code.
pub fn main() {
	if let Ok(opt_level) = env::var("OPT_LEVEL") {
		println!("cargo:rustc-cfg=opt_level={:?}", opt_level);
	}
}
