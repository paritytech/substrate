# Substrate Node Template Release Process

1. This release process has to be run in a github checkout Substrate directory with your work
committed into `https://github.com/paritytech/substrate/`, because the build script will check
the existence of your current git commit ID in the remote repository.

	Assume you are in root directory of Substrate. Run:

	```bash
	cd scripts/ci/
	./node-template-release.sh <output tar.gz file>
	```

2. Expand the output tar gzipped file and replace files in current Substrate Node Template
by running the following command.

	```bash
	# This is where the tar.gz file uncompressed
	cd substrate-node-template
	# rsync with force copying. Note the slash at the destination directory is important
	rsync -avh * <destination node-template directory>/
	# For dry-running add `-n` argument
	# rsync -avhn * <destination node-template directory>/
	```

	The above command only copies existing files from the source to the destination, but does not
	delete files/directories that are removed from the source. So you need to manually check and
	remove them in the destination.

3. There is a `Cargo.toml` file in the root directory. Inside, dependencies are listed form and
linked to a certain git commit in Substrate remote repository, such as:

	```toml
	sp-core = { version = "7.0.0", git = "https://github.com/paritytech/substrate.git", rev = "de80d0107336a9c7a2efdc0199015e4d67fcbdb5", default-features = false }
	```

	We will update each of them to link to the Rust	[crate registry](https://crates.io/).
After confirming the versioned package is published in the crate, the above will become:

	```toml
	[workspace.dependencies]
	sp-core = { version = "7.0.0", default-features = false }
	```

	P.S: This step can be automated if we update `node-template-release` package in
	`scripts/ci/node-template-release`.

4. Once the `Cargo.toml` is updated, compile and confirm that the Node Template builds. Then commit
the changes to a new branch in [Substrate Node Template](https://github.com/substrate-developer-hub/substrate-node-template), and make a PR.

	> Note that there is a chance the code in Substrate Node Template works with the linked Substrate git
	commit but not with published packages due to the latest (as yet) unpublished features. In this case,
	rollback that section of the Node Template to its previous version to ensure the Node Template builds.

5. Once the PR is merged, tag the merged commit in master branch with the version number
`vX.Y.Z+A` (e.g. `v3.0.0+1`). The `X`(major), `Y`(minor), and `Z`(patch) version number should
follow Substrate release version. The last digit is any significant fixes made in the Substrate
Node Template apart from Substrate. When the Substrate version is updated, this digit is reset to 0.

## Troubleshooting

- Running the script `./node-template-release.sh <output tar.gz file>`, after all tests passed
	successfully, seeing the following error message:

	```
	thread 'main' panicked at 'Creates output file: Os { code: 2, kind: NotFound, message: "No such file or directory" }', src/main.rs:250:10
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
	```

	This is likely due to that your output path is not a valid `tar.gz` filename or you don't have write
	permission to the destination. Try with a simple output path such as `~/node-tpl.tar.gz`.
