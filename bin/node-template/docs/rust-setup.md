---
title: Installation
---

This guide is for reference only, please check the latest information on getting starting with Substrate 
[here](https://docs.substrate.io/main-docs/install/).

This page will guide you through the **2 steps** needed to prepare a computer for **Substrate** development.
Since Substrate is built with [the Rust programming language](https://www.rust-lang.org/), the first
thing you will need to do is prepare the computer for Rust development - these steps will vary based
on the computer's operating system. Once Rust is configured, you will use its toolchains to interact
with Rust projects; the commands for Rust's toolchains will be the same for all supported,
Unix-based operating systems.

## Build dependencies

Substrate development is easiest on Unix-based operating systems like macOS or Linux. The examples
in the [Substrate Docs](https://docs.substrate.io) use Unix-style terminals to demonstrate how to
interact with Substrate from the command line.

### Ubuntu/Debian

Use a terminal shell to execute the following commands:

```bash
sudo apt update
# May prompt for location information
sudo apt install -y git clang curl libssl-dev llvm libudev-dev
```

### Arch Linux

Run these commands from a terminal:

```bash
pacman -Syu --needed --noconfirm curl git clang
```

### Fedora

Run these commands from a terminal:

```bash
sudo dnf update
sudo dnf install clang curl git openssl-devel
```

### OpenSUSE

Run these commands from a terminal:

```bash
sudo zypper install clang curl git openssl-devel llvm-devel libudev-devel
```

### macOS

> **Apple M1 ARM**
> If you have an Apple M1 ARM system on a chip, make sure that you have Apple Rosetta 2
> installed through `softwareupdate --install-rosetta`. This is only needed to run the
> `protoc` tool during the build. The build itself and the target binaries would remain native.

Open the Terminal application and execute the following commands:

```bash
# Install Homebrew if necessary https://brew.sh/
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install.sh)"

# Make sure Homebrew is up-to-date, install openssl
brew update
brew install openssl
```

### Windows

**_PLEASE NOTE:_** Native Windows development of Substrate is _not_ very well supported! It is _highly_
recommend to use [Windows Subsystem Linux](https://docs.microsoft.com/en-us/windows/wsl/install-win10)
(WSL) and follow the instructions for [Ubuntu/Debian](#ubuntudebian).
Please refer to the separate
[guide for native Windows development](https://docs.substrate.io/main-docs/install/windows/).

## Rust developer environment

This guide uses <https://rustup.rs> installer and the `rustup` tool to manage the Rust toolchain.
First install and configure `rustup`:

```bash
# Install
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
# Configure
source ~/.cargo/env
```

Configure the Rust toolchain to default to the latest stable version, and add the wasm target:

```bash
rustup default stable
rustup update
rustup target add wasm32-unknown-unknown
```

## Test your set-up

Now the best way to ensure that you have successfully prepared a computer for Substrate
development is to follow the steps in [our first Substrate tutorial](https://docs.substrate.io/tutorials/v3/create-your-first-substrate-chain/).

## Troubleshooting Substrate builds

Sometimes you can't get the Substrate node template
to compile out of the box. Here are some tips to help you work through that.

### Rust configuration check

To see what Rust toolchain you are presently using, run:

```bash
rustup show
```

This will show something like this (Ubuntu example) output:

```text
Default host: x86_64-unknown-linux-gnu
rustup home:  /home/user/.rustup

installed toolchains
--------------------

stable-x86_64-unknown-linux-gnu (default)
nightly-2020-10-06-x86_64-unknown-linux-gnu
nightly-x86_64-unknown-linux-gnu

installed targets for active toolchain
--------------------------------------

wasm32-unknown-unknown
x86_64-unknown-linux-gnu

active toolchain
----------------

stable-x86_64-unknown-linux-gnu (default)
rustc 1.50.0 (cb75ad5db 2021-02-10)
```

As you can see above, the default toolchain is stable, and the
`nightly-x86_64-unknown-linux-gnu` toolchain as well as its `wasm32-unknown-unknown` target is installed.
You also see that `nightly-2020-10-06-x86_64-unknown-linux-gnu` is installed, but is not used unless explicitly defined as illustrated in the [specify your nightly version](#specifying-nightly-version)
section.

### WebAssembly compilation

Substrate uses [WebAssembly](https://webassembly.org) (Wasm) to produce portable blockchain
runtimes. You will need to configure your Rust compiler to use
[`nightly` builds](https://doc.rust-lang.org/book/appendix-07-nightly-rust.html) to allow you to
compile Substrate runtime code to the Wasm target.

> There are upstream issues in Rust that need to be resolved before all of Substrate can use the stable Rust toolchain.
> [This is our tracking issue](https://github.com/paritytech/substrate/issues/1252) if you're curious as to why and how this will be resolved.

#### Latest for Substrate `master`

Developers who are building Substrate _itself_ should always use the latest bug-free versions of
Rust stable. To ensure your Rust compiler is always up to date, you should run:

```bash
rustup update
rustup target add wasm32-unknown-unknown
```

> NOTE: It may be necessary to occasionally rerun `rustup update` if a change in the upstream Substrate
> codebase depends on a new feature of the Rust compiler. When you do this, both your nightly
> and stable toolchains will be pulled to the most recent release, and for nightly, it is
> generally _not_ expected to compile WASM without error (although it very often does).
> Be sure to [specify your nightly version](#specifying-nightly-version) if you get WASM build errors
> from `rustup` and [downgrade nightly as needed](#downgrading-rust-nightly).

#### Rust toolchain

If you want to guarantee that your build works on your computer as you update Rust and other dependencies, 
you should use a specific Rust stable version that is known to be compatible with the version of Substrate 
they are using; this version will vary from project to project, and different projects may use different 
mechanisms to communicate this version to developers. For instance, the Polkadot client specifies 
this information in its [release notes](https://github.com/paritytech/polkadot/releases).

In case you need to specify a specific stable version of Rust, you can use rustup override command as follows:
```bash
# Specify the specific stable toolchain version in the command below:
rustup override set stable-<version>
```

For older versions of our project that use Rust nightly, you can still specify a version in the following way:
```bash
# Specify the specific nightly toolchain in the date below:
rustup install nightly-<yyyy-MM-dd>
```

#### Wasm toolchain

Now, configure the stable version to work with the Wasm compilation target:

```bash
rustup target add wasm32-unknown-unknown
```

### Specifying Rust version

Use the WASM_BUILD_TOOLCHAIN environment variable to specify the Rust stable version a Substrate project
 should use for Wasm compilation:

```bash
WASM_BUILD_TOOLCHAIN=stable-<version> cargo build --release
```

Replace <version> with the desired version number. For example, if you want to use Rust 1.52.1, 
you would enter:

```bash
WASM_BUILD_TOOLCHAIN=stable-1.52.1 cargo build --release
```

> Note: This only builds the runtime with the specified stable Rust. The rest of the project will be compiled 
> with your default toolchain, i.e. the latest installed stable toolchain.

### Changing Rust version

If your computer is configured to use a different version of Rust and you would like to change to a 
specific stable version, follow these steps:

```bash
rustup uninstall stable
rustup install stable-<version>
rustup target add wasm32-unknown-unknown
```
