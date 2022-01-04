// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

fn main() {
	#[cfg(feature = "cli")]
	cli::main();
}

#[cfg(feature = "cli")]
mod cli {
	include!("src/cli.rs");

	use sc_cli::structopt::clap::Shell;
	use std::{env, fs, path::Path};
	use substrate_build_script_utils::{generate_cargo_keys, rerun_if_git_head_changed};

	pub fn main() {
		build_shell_completion();
		generate_cargo_keys();

		rerun_if_git_head_changed();
	}

	/// Build shell completion scripts for all known shells
	/// Full list in https://github.com/kbknapp/clap-rs/blob/e9d0562a1dc5dfe731ed7c767e6cee0af08f0cf9/src/app/parser.rs#L123
	fn build_shell_completion() {
		for shell in &[Shell::Bash, Shell::Fish, Shell::Zsh, Shell::Elvish, Shell::PowerShell] {
			build_completion(shell);
		}
	}

	/// Build the shell auto-completion for a given Shell
	fn build_completion(shell: &Shell) {
		let outdir = match env::var_os("OUT_DIR") {
			None => return,
			Some(dir) => dir,
		};
		let path = Path::new(&outdir)
			.parent()
			.unwrap()
			.parent()
			.unwrap()
			.parent()
			.unwrap()
			.join("completion-scripts");

		fs::create_dir(&path).ok();

		Cli::clap().gen_completions("substrate-node", *shell, &path);
	}
}
