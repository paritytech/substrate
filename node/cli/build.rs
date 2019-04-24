// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
use cli::{NoCustom, CoreParams};

use std::{fs, env, path::Path};

use structopt::{StructOpt, clap::Shell};

fn main() {
	build_shell_completion();
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
		.parent().unwrap()
		.parent().unwrap()
		.parent().unwrap()
		.join("completion-scripts");

	fs::create_dir(&path).ok();

	CoreParams::<NoCustom, NoCustom>::clap().gen_completions("substrate-node", *shell, &path);
}
