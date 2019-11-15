use vergen::{ConstantsFlags, generate_cargo_keys};

const ERROR_MSG: &str = "Failed to generate metadata files";

fn main() {
	generate_cargo_keys(ConstantsFlags::SHA_SHORT).expect(ERROR_MSG);

	build_script_utils::rerun_if_git_head_changed();
}
