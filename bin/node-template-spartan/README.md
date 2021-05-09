<div align="center">

  <h1><code>node-template-spartan</code></h1>

  <strong>A Substrate Node Template which implements Spartan Proof-of-Capacity (PoC) consensus.</strong>

</div>

# Overview

This repo is an implementation of Spartan Proof-of-Capacity (PoC) consensus for the Substrate framework, organized as a Substrate pallet and several dependencies. It is largely based on a fork of `pallet_babe`, with which it shares many similarities. This work is supported by a [Web 3 Foundation grant](https://github.com/w3f/Open-Grants-Program/blob/master/applications/spartan_poc_consensus_module.md) to develop PoC consensus for Substrate. PoC is a generic term for consensus based on disk space, including proofs of space, storage, space-time, and replication.

Spartan is a simple and secure PoC consensus protocol, which replaces 'one-cpu-one-vote' with 'one-disk-one-vote'. This allows for mass participation in consensus by ordinary users with commodity hardware. Since PoC consensus is energy-efficient, widespread adoption is also environmentally sustainable. Spartan retains several key features of Nakamoto Consensus, including: the longest-chain fork-choice rule, dynamic availability (i.e., it is permissionless), and the honest majority assumption. Similar to proof-of-stake protocols, there is no mining delay, so we instead employ a round based notion of time, which is almost identical to the Ouroborous family of protocols and BABE.

To learn more about Spartan, read the [design document](https://github.com/subspace/substrate/blob/poc/frame/spartan/design.md).

Spartan is a stepping stone towards the larger goal of deploying [Subspace](https://www.subspace.network/) as a parachain on the Polkadot Network. Subspace is a proof-of-storage blockchain that resolves the farmer's dilemma, to learn more read our <a href="https://drive.google.com/file/d/1v847u_XeVf0SBz7Y7LEMXi72QfqirstL/view">white paper</a>.

# Node Template Spartan

A fresh FRAME-based [Substrate](https://www.substrate.io/) node, modified for Spartan PoC consensus :rocket:

Based on a fork of Substrate Node Template.

**Notes:** The code is un-audited and not production ready, use it at your own risk.

## Getting Started

Follow these steps to get started with the Spartan Node Template :hammer_and_wrench:

### Run In Development Mode

#### Install Rust

First, complete the [basic Rust setup instructions](./doc/rust-setup.md).

#### Install Dependencies
If you have not previously installed the `gmp_mpfr_sys` crate, follow these [instructions](https://docs.rs/gmp-mpfr-sys/1.3.0/gmp_mpfr_sys/index.html#building-on-gnulinux).

On Linux, RocksDB requires Clang

```bash
sudo apt-get install llvm clang gcc make m4
```

#### Setup Spartan-Farmer
Create 1 GiB plot according to following instructions: https://github.com/subspace/spartan-farmer

#### Install and Run Node

This will run a node-template-spartan in one terminal and a spartan-farmer farming in a second terminal.
The node will send slot notification challenges to the farmer.
If the farmer finds a valid solution it will reply, and the node will produce a new block.

```bash
# Install Node
git clone https://github.com/subspace/substrate.git
cd substrate

# Build and run Node (first terminal)
cargo +nightly run --bin node-template-spartan -- --dev --tmp

# wait for the client to start before continuing...

# Run Farmer (second terminal)
cd /back/to/spartan-farmer
cargo +nightly run farm
```

NOTE: Above commands require nightly compiler for now, make sure to install it if you don't have one yet:
```
rustup toolchain install nightly
```

### Run with Docker

First, install [Docker](https://docs.docker.com/get-docker/) and
[Docker Compose](https://docs.docker.com/compose/install/).

Create volume for plot and initialize 1 GiB plot (should take a few seconds to a few minutes):
```bash
docker volume create spartan-farmer
docker run --rm -it --name spartan-farmer --mount source=spartan-farmer,target=/var/spartan subspacelabs/spartan-farmer plot 256000 spartan
```

Start a single node development chain:
```bash
docker run --rm --init -it --name node-template-spartan subspacelabs/node-template-spartan --dev --tmp
```

Once node is running, you can connect farmer to it by running following in a separate terminal:
```bash
docker run --rm --init -it --name spartan-farmer --mount source=spartan-farmer,target=/var/spartan --net container:node-template-spartan subspacelabs/spartan-farmer farm
```

Now you should see block production in the first terminal where node is running.

### Run Tests

```bash

# PoC tests
cd substrate/client/consensus/poc
cargo test

# Spartan tests
cd substrate/frame/spartan
cargo test

# Farmer tests
cd spartan-farmer
cargo test

```

### Embedded Docs

Once the project has been built, the following command can be used to explore all parameters and
subcommands:

```bash
cargo run --bin node-template-spartan -- -h
```

## Run

The provided `cargo run` command will launch a temporary node and its state will be discarded after
you terminate the process. After the project has been built, there are other ways to launch the
node.

### Single-Node Development Chain

This command will start the single-node development chain with persistent state:

```bash
cargo run --bin node-template-spartan -- --dev
```

Purge the development chain's state:

```bash
cargo run --bin node-template-spartan -- purge-chain --dev
```

Start the development chain with detailed logging:

```bash
RUST_BACKTRACE=1 cargo run --bin node-template-spartan -- -ldebug --dev
```
