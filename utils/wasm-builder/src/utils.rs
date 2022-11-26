use std::{env, fs, path::PathBuf, process::Command};

/// Copy `src` to `dst` if the `dst` does not exist or is different.
pub(crate) fn copy_file_if_changed(src: PathBuf, dst: PathBuf) {
	let src_file = fs::read_to_string(&src).ok();
	let dst_file = fs::read_to_string(&dst).ok();

	if src_file != dst_file {
		fs::copy(&src, &dst).unwrap_or_else(|_| {
			panic!("Copying `{}` to `{}` can not fail; qed", src.display(), dst.display())
		});
	}
}

/// Wraps a specific command which represents a cargo invocation.
#[derive(Debug)]
pub(crate) struct CargoCommand {
	program: String,
	args: Vec<String>,
}

impl CargoCommand {
	pub(crate) fn new(program: &str) -> Self {
		CargoCommand { program: program.into(), args: Vec::new() }
	}

	pub(crate) fn new_with_args(program: &str, args: &[&str]) -> Self {
		CargoCommand {
			program: program.into(),
			args: args.iter().map(ToString::to_string).collect(),
		}
	}

	pub(crate) fn command(&self) -> Command {
		let mut cmd = Command::new(&self.program);
		cmd.args(&self.args);
		cmd
	}

	/// Check if the supplied cargo command is a nightly version
	pub(crate) fn is_nightly(&self) -> bool {
		// `RUSTC_BOOTSTRAP` tells a stable compiler to behave like a nightly. So, when this env
		// variable is set, we can assume that whatever rust compiler we have, it is a nightly
		// compiler. For "more" information, see:
		// https://github.com/rust-lang/rust/blob/fa0f7d0080d8e7e9eb20aa9cbf8013f96c81287f/src/libsyntax/feature_gate/check.rs#L891
		env::var("RUSTC_BOOTSTRAP").is_ok() ||
			self.command()
				.arg("--version")
				.output()
				.map_err(|_| ())
				.and_then(|o| String::from_utf8(o.stdout).map_err(|_| ()))
				.unwrap_or_default()
				.contains("-nightly")
	}
}

/// Wraps a [`CargoCommand`] and the version of `rustc` the cargo command uses.
pub(crate) struct CargoCommandVersioned {
	command: CargoCommand,
	version: String,
}

impl CargoCommandVersioned {
	pub(crate) fn new(command: CargoCommand, version: String) -> Self {
		Self { command, version }
	}

	/// Returns the `rustc` version.
	pub(crate) fn rustc_version(&self) -> &str {
		&self.version
	}
}

impl std::ops::Deref for CargoCommandVersioned {
	type Target = CargoCommand;

	fn deref(&self) -> &CargoCommand {
		&self.command
	}
}
