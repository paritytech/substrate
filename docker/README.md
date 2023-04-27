# Substrate Builder Docker Image

The Docker image in this folder is a `builder` image. It is self contained and allows users to build the binaries themselves.
There is no requirement on having Rust or any other toolchain installed but a working Docker environment.

Unlike the `parity/polkadot` image which contains a single binary (`polkadot`!) used by default, the image in this folder builds and contains several binaries and you need to provide the name of the binary to be called.

You should refer to the [.Dockerfile](./substrate_builder.Dockerfile) for the actual list. At the time of editing, the list of included binaries is:

- substrate
- subkey
- node-template
- chain-spec-builder

First, install [Docker](https://docs.docker.com/get-docker/).

Then to generate the latest parity/substrate image. Please run:
```sh
./build.sh
```

> If you wish to create a debug build rather than a production build, then you may modify the [.Dockerfile](./substrate_builder.Dockerfile) replacing `cargo build --locked --release` with just `cargo build --locked` and replacing `target/release` with `target/debug`. 

> If you get an error that a tcp port address is already in use then find an available port to use for the host port in the [.Dockerfile](./substrate_builder.Dockerfile).

The image can be used by passing the selected binary followed by the appropriate tags for this binary.

Your best guess to get started is to pass the `--help flag`. Here are a few examples:

- `./run.sh substrate --version`
- `./run.sh subkey --help`
- `./run.sh node-template --version`
- `./run.sh chain-spec-builder --help`

Then try running the following command to start a single node development chain using the Substrate Node Template binary `node-template`:

```sh
./run.sh node-template --dev --ws-external
```

Note: It is recommended to provide a custom `--base-path` to store the chain database. For example:

```sh
# Run Substrate Node Template without re-compiling
./run.sh node-template --dev --ws-external --base-path=/data
```

> To print logs follow the [Substrate debugging instructions](https://docs.substrate.io/test/debug/).

```sh
# Purge the local dev chain
./run.sh node-template purge-chain --dev --base-path=/data -y
```
