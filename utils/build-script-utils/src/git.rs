// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use std::{env, fs, fs::File, io, io::Read, path::PathBuf};

/// Make sure the calling `build.rs` script is rerun when `.git/HEAD` or the ref of `.git/HEAD`
/// changed.
///
/// The file is searched from the `CARGO_MANIFEST_DIR` upwards. If the file can not be found,
/// a warning is generated.
pub fn rerun_if_git_head_changed() {
	let mut manifest_dir = PathBuf::from(
		env::var("CARGO_MANIFEST_DIR").expect("`CARGO_MANIFEST_DIR` is always set by cargo."),
	);
	let manifest_dir_copy = manifest_dir.clone();

	while manifest_dir.parent().is_some() {
		match get_git_paths(&manifest_dir) {
			Err(err) => {
				eprintln!("cargo:warning=Unable to read the Git repository: {}", err);

				return;
			}
			Ok(None) => {}
			Ok(Some(paths)) => {
				for p in paths {
					println!("cargo:rerun-if-changed={}", p.display());
				}

				return;
			}
		}

		manifest_dir.pop();
	}

	println!(
		"cargo:warning=Could not find `.git/HEAD` searching from `{}` upwards!",
		manifest_dir_copy.display(),
	);
}

// Code taken from https://github.com/rustyhorde/vergen/blob/8d522db8c8e16e26c0fc9ea8e6b0247cbf5cca84/src/output/envvar.rs
fn get_git_paths(path: &PathBuf) -> Result<Option<Vec<PathBuf>>, io::Error> {
	let git_dir_or_file = path.join(".git");

	if let Ok(metadata) = fs::metadata(&git_dir_or_file) {
		if metadata.is_dir() {
			// Echo the HEAD path
			let git_head_path = git_dir_or_file.join("HEAD");

			// Determine where HEAD points and echo that path also.
			let mut f = File::open(&git_head_path)?;
			let mut git_head_contents = String::new();
			let _ = f.read_to_string(&mut git_head_contents)?;
			let ref_vec: Vec<&str> = git_head_contents.split(": ").collect();

			if ref_vec.len() == 2 {
				let current_head_file = ref_vec[1];
				let git_refs_path = git_dir_or_file.join(current_head_file);

				Ok(Some(vec![git_head_path, git_refs_path]))
			} else {
				Err(io::Error::new(
					io::ErrorKind::Other,
					"You are most likely in a detached HEAD state",
				))
			}
		} else if metadata.is_file() {
			// We are in a worktree, so find out where the actual worktrees/<name>/HEAD file is.
			let mut git_file = File::open(&git_dir_or_file)?;
			let mut git_contents = String::new();
			let _ = git_file.read_to_string(&mut git_contents)?;
			let dir_vec: Vec<&str> = git_contents.split(": ").collect();
			let git_path = dir_vec[1].trim();

			// Echo the HEAD psth
			let git_head_path = PathBuf::from(git_path).join("HEAD");

			// Find out what the full path to the .git dir is.
			let mut actual_git_dir = PathBuf::from(git_path);
			actual_git_dir.pop();
			actual_git_dir.pop();

			// Determine where HEAD points and echo that path also.
			let mut f = File::open(&git_head_path)?;
			let mut git_head_contents = String::new();
			let _ = f.read_to_string(&mut git_head_contents)?;
			let ref_vec: Vec<&str> = git_head_contents.split(": ").collect();

			if ref_vec.len() == 2 {
				let current_head_file = ref_vec[1];
				let git_refs_path = actual_git_dir.join(current_head_file);

				Ok(Some(vec![git_head_path, git_refs_path]))
			} else {
				Err(io::Error::new(
					io::ErrorKind::Other,
					"You are most likely in a detached HEAD state",
				))
			}
		} else {
			Err(io::Error::new(
				io::ErrorKind::Other,
				"Invalid .git format (Not a directory or a file)",
			))
		}
	} else {
		Ok(None)
	}
}
