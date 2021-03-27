# Node Template Release Process

1. It has to be in a github checkout directory with your current work committed into
`https://github.com/paritytech/substrate/`, because this is where the build script will check out
from. Assume you are in root directory of Substrate. Run:

	```bash
	cd .maintain/
	./node-template-release.sh <output tar.gz file>
	```

2. Expand the output tar gzipped file and replace files in current Substrate Node Template
by running the following command.

	```bash
	cd substrate-node-template
	# Note the slash at the destination directory is important
	rsync -rvu . <destination node-template directory>/
	```

3. Commit the changes to a new branch in [Substrate Node Template](https://github.com/substrate-developer-hub/substrate-node-template), and make a PR.

4. Once the PR is merged, tag the merged commit in master branch with the version number
`vX.Y.Z+A` (e.g. `v3.0.0+1`). The `X`(major), `Y`(minor), and `Z`(patch) version number should
follow Substrate release version. The last digit is any significant fixes made in the Substrate
Node Template apart from Substrate. When the Substrate version is updated, this digit is reset to 0.

## Troubleshooting

1. Running the script `./node-template-release.sh <output tar.gz file>`, after all tests passed
	successfully, seeing the following error message:

	```
	thread 'main' panicked at 'Creates output file: Os { code: 2, kind: NotFound, message: "No such file or directory" }', src/main.rs:250:10
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
	```
