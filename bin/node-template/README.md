[![Instant hacking via Playground](https://img.shields.io/badge/Playground-node_template-brightgreen?logo=Parity%20Substrate)](https://playground-staging.substrate.dev/?deploy=node-template)[The Substrate Playground](https://playground-staging.substrate.dev/?deploy=node-template) is our
online development environment (IDE) that allows developers to take advantage of a pre-configured container
with pre-compiled build artifacts. 

# Substrate Node Template

A new FRAME-based Substrate node, ready for hacking :rocket:

## Local Development

Follow these steps to prepare the local environment for Substrate development :hammer_and_wrench:

### Simple Setup

Install all the required dependencies with a single command (be patient, this can take up
to 30 minutes).

```bash
curl https://getsubstrate.io -sSf | bash -s -- --fast
```

### Manual Setup

Manual installation for Linux-based systems can be found below; additional informatoin can be found at
[substrate.dev](https://substrate.dev/docs/en/knowledgebase/getting-started/#manual-installation).

Install Rust:

```bash
curl https://sh.rustup.rs -sSf | sh
```

Initialize the Wasm Build environment:

```bash
./scripts/init.sh
```

### Build

Once the local development environment is complied, the node template can be built. The node template allows developers a working runtime which you can use to quickly get started building your own custom blockchain utilizing all the capacities of [FRAME](https://substrate.dev/docs/en/knowledgebase/runtime/frame).

Utilize the command line to build the [Wasm](https://substrate.dev/docs/en/knowledgebase/advanced/executor#wasm-execution)
and [native](https://substrate.dev/docs/en/knowledgebase/advanced/executor#native-execution) code:

```bash
cargo build --release
```

## Playground [![Try on playground](https://img.shields.io/badge/Playground-node_template-brightgreen?logo=Parity%20Substrate)](https://playground-staging.substrate.dev/?deploy=node-template)


## Run

### Single Node Development Chain

Purge any existing developer chain state:

```bash
./target/release/node-template purge-chain --dev
```

Start a new development chain:

```bash
./target/release/node-template --dev
```

Detailed logs may be shown by running the node with the following environment variables set:
`RUST_LOG=debug RUST_BACKTRACE=1 cargo run -- -lruntime=debug --dev`.

### Multi-Node Local Testnet

If developers want to see the multi-node consensus algorithm running locally, then developers can create a local
testnet with two validator nodes for Alice and Bob, who are the initial authorities of the genesis
chain that have been endowed with testnet units.

Optionally, define each node with a name and expose them so they are listed on the Polkadot
[telemetry site](https://telemetry.polkadot.io/#/Local%20Testnet).

Note: you'll need two terminal windows open.

We'll start Alice's substrate node first on default TCP port 30333 with her chain database stored
locally at `/tmp/alice`. The bootnode ID of her node is
`QmRpheLN4JWdAnY7HGJfWFNbfkQCb6tFf4vvA6hgjMZKrR`, which is generated from the `--node-key` value
that we specify below:

```bash
cargo run -- \
  --base-path /tmp/alice \
  --chain=local \
  --alice \
  --node-key 0000000000000000000000000000000000000000000000000000000000000001 \
  --telemetry-url 'ws://telemetry.polkadot.io:1024 0' \
  --validator
```

In the second terminal, we'll start Bob's substrate node on a different TCP port of 30334, and with
his chain database stored locally at `/tmp/bob`. We'll specify a value for the `--bootnodes` option
that will connect his node to Alice's bootnode ID on TCP port 30333:

```bash
cargo run -- \
  --base-path /tmp/bob \
  --bootnodes /ip4/127.0.0.1/tcp/30333/p2p/QmRpheLN4JWdAnY7HGJfWFNbfkQCb6tFf4vvA6hgjMZKrR \
  --chain=local \
  --bob \
  --port 30334 \
  --telemetry-url 'ws://telemetry.polkadot.io:1024 0' \
  --validator
```

Additional CLI usage options are available and may be shown by running `cargo run -- --help`.

## Generate Your Own Substrate Node Template

Generate a Substrate node template based on a particular Substrate
version/commit by running following commands:

```bash
# git clone from the main Substrate repo
git clone https://github.com/paritytech/substrate.git
cd substrate

# Switch to a particular branch or commit of the Substrate repo your node-template based on
git checkout <branch/tag/sha1>

# Run the helper script to generate a node template.
# This script compiles Substrate and takes a while to complete. It takes a relative file path
#   from the current dir. to output the compressed node template.
.maintain/node-template-release.sh ../node-template.tar.gz
```

Please note that this generally outputs a more constant support by appending with the releases
provided within [the Substrate Node Template repository](https://github.com/substrate-developer-hub/substrate-node-template).
