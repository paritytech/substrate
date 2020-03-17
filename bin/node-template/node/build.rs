use sc_cli;

fn main() {
	sc_cli::generate_cargo_keys();

	sc_cli::rerun_if_git_head_changed();
}
