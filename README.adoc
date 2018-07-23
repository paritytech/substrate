# Polkadot

Implementation of a https://polkadot.network node in Rust.

## To play

If you'd like to play with Polkadot, you'll need to install a client like this
one. First, get Rust (1.26.1 or later) and the support software if you don't already have it:

```
curl https://sh.rustup.rs -sSf | sh
sudo apt install make clang pkg-config libssl-dev
```

Then, install Polkadot PoC-2:

```
cargo install --git https://github.com/paritytech/polkadot.git --branch v0.2 polkadot
```

You'll now have a `polkadot` binary installed to your `PATH`. You can drop the
`--branch v0.2` or run `cargo install --git https://github.com/paritytech/polkadot.git polkadot`
to get the very latest version of Polkadot, but these instructions might not work in that case.

### Krumme Lanke Testnet

You will connect to the global Krumme Lanke testnet by default. To do this, just use:

```
polkadot
```

If you want to do anything on it (not that there's much to do), then you'll need
to get some Krumme Lanke DOTs. Ask in the Polkadot watercooler.

### Development

You can run a simple single-node development "network" on your machine by
running in a terminal:

```
polkadot --dev
```

You can muck around by cloning and building the http://github.com/paritytech/polka-ui and http://github.com/paritytech/polkadot-ui or just heading to https://polkadot.js.org/apps.

## Local Two-node Testnet

If you want to see the multi-node consensus algorithm in action locally, then
you can create a local testnet. You'll need two terminals open. In one, run:

```
polkadot --chain=local --validator --key Alice -d /tmp/alice
```

and in the other, run:

```
polkadot --chain=local --validator --key Bob -d /tmp/bob --port 30334 --bootnodes '/ip4/127.0.0.1/tcp/30333/p2p/ALICE_BOOTNODE_ID_HERE'
```

Ensure you replace `ALICE_BOOTNODE_ID_HERE` with the node ID from the output of
the first terminal.

## Hacking on Polkadot

If you'd actually like hack on Polkadot, you can just grab the source code and
build it. Ensure you have Rust and the support software installed:

```
curl https://sh.rustup.rs -sSf | sh
rustup update nightly
rustup target add wasm32-unknown-unknown --toolchain nightly
rustup update stable
cargo install --git https://github.com/alexcrichton/wasm-gc
sudo apt install cmake pkg-config libssl-dev
```

Then, grab the Polkadot source code:

```
git clone https://github.com/paritytech/polkadot.git
cd polkadot
```

Then build the code:

```
./build.sh  # Builds the WebAssembly binaries
cargo build # Builds all native code
```

You can run the tests if you like:

```
cargo test --all
```

You can start a development chain with:

```
cargo run -- --dev
```

## Shell completion

The Polkadot cli command supports shell auto-completion. For this to work, you will need to run the completion script matching you build and system.

Assuming you built a release version using `cargo build --release` and use `bash` run the following:
```
source target/release/completion-scripts/polkadot.bash
```

You can find completion scripts for:
- bash
- fish
- zsh
- elvish
- powershell

To make this change persistent, you can proceed as follow:
### First install
```
COMPL_DIR=$HOME/.completion
mkdir -p $COMPL_DIR
cp -f target/release/completion-scripts/polkadot.bash $COMPL_DIR/
echo "source $COMPL_DIR/polkadot.bash" >> $HOME/.bash_profile
source $HOME/.bash_profile
```

### Update
When you build a new version of Polkadot, the following will ensure you auto-completion script matches the current binary:
```
COMPL_DIR=$HOME/.completion
mkdir -p $COMPL_DIR
cp -f target/release/completion-scripts/polkadot.bash $COMPL_DIR/
source $HOME/.bash_profile
```

