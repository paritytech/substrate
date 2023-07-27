// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! # Subkey
//!
//! Subkey is a commandline utility included with Substrate. It allows generating and restoring keys
//! for Substrate based chains such as Polkadot, Kusama and a growing number of parachains and
//! Substrate based projects.

//! `subkey` provides a few sub-commands to generate keys, check keys, sign messages, verify
//! messages, etc...
//!
//! You can see the full list of commands with `subkey --help`. Most commands have additional help
//! available with for instance `subkey generate --help` for the `generate` command.
//!
//! ## Safety first
//!
//! `subkey` does not need an internet connection to work. Indeed, for the best security, you should
//! be using `subkey` on a machine that is **not connected** to the internet.
//!
//! `subkey` deals with **seeds** and **private keys**. Make sure to use `subkey` in a safe
//! environment (ie. no one looking over your shoulder) and on a safe computer (ie. no one able to
//! check your command history).
//!
//! If you save any output of `subkey` into a file, make sure to apply proper permissions and/or
//! delete the file as soon as possible.
//!
//! ## Usage
//!
//! The following guide explains *some* of the `subkey` commands. For the full list and the most up
//! to date documentation, make sure to check the integrated help with `subkey --help`.
//!
//! ### Install with Cargo
//!
//! You will need to have the Substrate build dependencies to install Subkey. Use the following two
//! commands to install the dependencies and Subkey, respectively:
//!
//! Command:
//!
//! ```bash
//! # Install only `subkey`, at a specific version of the subkey crate
//! cargo install --force subkey --git https://github.com/paritytech/substrate --version <SET VERSION> --locked
//! # If you run into issues building, you likely are missing deps defined in https://docs.substrate.io/install/
//! ```
//!
//! ### Run in a container
//!
//! ```bash
//! # Use `--pull=always` with the `latest` tag, or specify a version in a tag
//! docker run -it --pull=always docker.io/parity/subkey:latest <command to subkey>
//! ```
//!
//! ### Generate a random account
//!
//! Generating a new key is as simple as running:
//!
//! ```bash
//! subkey generate
//! ```
//!
//! The output looks similar to:
//!
//! ```text
//! Secret phrase `hotel forest jar hover kite book view eight stuff angle legend defense` is account:
//!   Secret seed:      0xa05c75731970cc7868a2fb7cb577353cd5b31f62dccced92c441acd8fee0c92d
//!   Public key (hex): 0xfec70cfbf1977c6965b5af10a4534a6a35d548eb14580594d0bc543286892515
//!   Account ID:       0xfec70cfbf1977c6965b5af10a4534a6a35d548eb14580594d0bc543286892515
//!   SS58 Address:     5Hpm9fq3W3dQgwWpAwDS2ZHKAdnk86QRCu7iX4GnmDxycrte
//! ```
//!
//! ---
//! ☠️ DO NT RE-USE ANY OF THE SEEDS AND SECRETS FROM THIS PAGE ☠️.
//!
//! You can read more about security and risks in [SECURITY.md](./SECURITY.md) and in the [Polkadot Wiki](https://wiki.polkadot.network/docs/learn-account-generation).
//!
//! ---
//!
//! The output above shows a **secret phrase** (also called **mnemonic phrase**) and the **secret
//! seed** (also called **Private Key**). Those 2 secrets are the pieces of information you MUST
//! keep safe and secret. All the other information below can be derived from those secrets.
//!
//! The output above also show the **public key** and the **Account ID**. Those are the independant
//! from the network where you will use the key.
//!
//! The **SS58 address** (or **Public Address**) of a new account is a reprensentation of the public
//! keys of an account for a given network (for instance Kusama or Polkadot).
//!
//! You can read more about the [SS58 format in the Substrate Docs](https://docs.substrate.io/reference/address-formats/) and see the list of reserved prefixes in the [SS58 Registry](https://github.com/paritytech/ss58-registry).
//!
//! For instance, considering the previous seed
//! `0xa05c75731970cc7868a2fb7cb577353cd5b31f62dccced92c441acd8fee0c92d` the SS58 addresses are:
//!
//! - Polkadot: `16m4J167Mptt8UXL8aGSAi7U2FnPpPxZHPrCgMG9KJzVoFqM`
//! - Kusama: `JLNozAv8QeLSbLFwe2UvWeKKE4yvmDbfGxTuiYkF2BUMx4M`
//!
//! ### Json output
//!
//! `subkey` can calso generate the output as *json*. This is useful for automation.
//!
//! command:
//!
//! ```bash
//! subkey generate --output-type json
//! ```
//!
//! output:
//!
//! ```json
//! {
//!   "accountId": "0xfec70cfbf1977c6965b5af10a4534a6a35d548eb14580594d0bc543286892515",
//!   "publicKey": "0xfec70cfbf1977c6965b5af10a4534a6a35d548eb14580594d0bc543286892515",
//!   "secretPhrase": "hotel forest jar hover kite book view eight stuff angle legend defense",
//!   "secretSeed": "0xa05c75731970cc7868a2fb7cb577353cd5b31f62dccced92c441acd8fee0c92d",
//!   "ss58Address": "5Hpm9fq3W3dQgwWpAwDS2ZHKAdnk86QRCu7iX4GnmDxycrte"
//! }
//! ```
//!
//! So if you only want to get the `secretSeed` for instance, you can use:
//!
//! command:
//!
//! ```bash
//! subkey generate --output-type json | jq -r .secretSeed
//! ```
//!
//! output:
//!
//! ```text
//! 0xa05c75731970cc7868a2fb7cb577353cd5b31f62dccced92c441acd8fee0c92d
//! ```
//!
//! ### Additional user-defined password
//!
//! `subkey` supports an additional user-defined secret that will be appended to the seed. Let's see
//! the following example:
//!
//! ```bash
//! subkey generate --password extra_secret
//! ```
//!
//! output:
//!
//! ```text
//! Secret phrase `soup lyrics media market way crouch elevator put moon useful question wide` is account:
//!   Secret seed:      0xe7cfd179d6537a676cb94bac3b5c5c9cb1550e846ac4541040d077dfbac2e7fd
//!   Public key (hex): 0xf6a233c3e1de1a2ae0486100b460b3ce3d7231ddfe9dadabbd35ab968c70905d
//!   Account ID:       0xf6a233c3e1de1a2ae0486100b460b3ce3d7231ddfe9dadabbd35ab968c70905d
//!   SS58 Address:     5He5pZpc7AJ8evPuab37vJF6KkFDqq9uDq2WXh877Qw6iaVC
//! ```
//!
//! Using the `inspect` command (see more details below), we see that knowning only the **secret
//! seed** is no longer sufficient to recover the account:
//!
//! ```bash
//! subkey inspect "soup lyrics media market way crouch elevator put moon useful question wide"
//! ```
//!
//! which recovers the account `5Fe4sqj2K4fRuzEGvToi4KATqZfiDU7TqynjXG6PZE2dxwyh` and not
//! `5He5pZpc7AJ8evPuab37vJF6KkFDqq9uDq2WXh877Qw6iaVC` as we expected. The additional user-defined
//! **password** (`extra_secret` in our example) is now required to fully recover the account. Let's
//! inspect the the previous mnemonic, this time passing also the required `password` as shown
//! below:
//!
//! ```bash
//! subkey inspect --password extra_secret "soup lyrics media market way crouch elevator put moon useful question wide"
//! ```
//!
//! This time, we properly recovered `5He5pZpc7AJ8evPuab37vJF6KkFDqq9uDq2WXh877Qw6iaVC`.
//!
//! ### Inspecting a key
//!
//! If you have *some data* about a key, `subkey inpsect` will help you discover more information
//! about it.
//!
//! If you have **secrets** that you would like to verify for instance, you can use:
//!
//! ```bash
//! subkey inspect < mnemonic | seed >
//! ```
//!
//! If you have only **public data**, you can see a subset of the information:
//!
//! ```bash
//! subkey inspect --public < pubkey | address >
//! ```
//!
//! **NOTE**: While you will be able to recover the secret seed from the mnemonic, the opposite is
//! not possible.
//!
//! **NOTE**: For obvious reasons, the **secrets** cannot be recovered from passing **public data**
//! such as `pubkey` or `address` as input.
//!
//! command:
//!
//! ```bash
//! subkey inspect 0xa05c75731970cc7868a2fb7cb577353cd5b31f62dccced92c441acd8fee0c92d
//! ```
//!
//! output:
//!
//! ```text
//! Secret Key URI `0xa05c75731970cc7868a2fb7cb577353cd5b31f62dccced92c441acd8fee0c92d` is account:
//!   Secret seed:      0xa05c75731970cc7868a2fb7cb577353cd5b31f62dccced92c441acd8fee0c92d
//!   Public key (hex): 0xfec70cfbf1977c6965b5af10a4534a6a35d548eb14580594d0bc543286892515
//!   Account ID:       0xfec70cfbf1977c6965b5af10a4534a6a35d548eb14580594d0bc543286892515
//!   SS58 Address:     5Hpm9fq3W3dQgwWpAwDS2ZHKAdnk86QRCu7iX4GnmDxycrte
//! ```
//!
//! ### Signing
//!
//! `subkey` allows using a **secret key** to sign a random message. The signature can then be
//! verified by anyone using your **public key**:
//!
//! ```bash
//! echo -n <msg> | subkey sign --suri <seed|mnemonic>
//! ```
//!
//! example:
//!
//! ```text
//! MESSAGE=hello
//! SURI=0xa05c75731970cc7868a2fb7cb577353cd5b31f62dccced92c441acd8fee0c92d
//! echo -n $MESSAGE | subkey sign --suri $SURI
//! ```
//!
//! output:
//!
//! ```text
//! 9201af3788ad4f986b800853c79da47155f2e08fde2070d866be4c27ab060466fea0623dc2b51f4392f4c61f25381a62848dd66c5d8217fae3858e469ebd668c
//! ```
//!
//! **NOTE**: Each run of the `sign` command will yield a different output. While each signature is
//! different, they are all valid.
//!
//! ### Verifying a signature
//!
//! Given a message, a signature and an address, `subkey` can verify whether the **message** has
//! been digitally signed by the holder (or one of the holders) of the **private key** for the given
//! **address**:
//!
//! ```bash
//! echo -n <msg> | subkey verify <sig> <address>
//! ```
//!
//! example:
//!
//! ```bash
//! MESSAGE=hello
//! URI=0xfec70cfbf1977c6965b5af10a4534a6a35d548eb14580594d0bc543286892515
//! SIGNATURE=9201af3788ad4f986b800853c79da47155f2e08fde2070d866be4c27ab060466fea0623dc2b51f4392f4c61f25381a62848dd66c5d8217fae3858e469ebd668c
//! echo -n $MESSAGE | subkey verify $SIGNATURE $URI
//! ```
//!
//! output:
//!
//! ```text
//! Signature verifies correctly.
//! ```
//!
//! A failure looks like:
//!
//! ```text
//! Error: SignatureInvalid
//! ```
//!
//! ### Using the vanity generator
//!
//! You can use the included vanity generator to find a seed that provides an address which includes
//! the desired pattern. Be warned, depending on your hardware this may take a while.
//!
//! command:
//!
//! ```bash
//! subkey vanity --network polkadot --pattern bob
//! ```
//!
//! output:
//!
//! ```text
//! Generating key containing pattern 'bob'
//! best: 190 == top: 189
//! Secret Key URI `0x8c9a73097f235b84021a446bc2826a00c690ea0be3e0d81a84931cb4146d6691` is account:
//!   Secret seed:      0x8c9a73097f235b84021a446bc2826a00c690ea0be3e0d81a84931cb4146d6691
//!   Public key (hex): 0x1a8b32e95c1f571118ea0b84801264c3c70f823e320d099e5de31b9b1f18f843
//!   Account ID:       0x1a8b32e95c1f571118ea0b84801264c3c70f823e320d099e5de31b9b1f18f843
//!   SS58 Address:     1bobYxBPjZWRPbVo35aSwci1u5Zmq8P6J2jpa4kkudBZMqE
//! ```
//!
//! `Bob` now got a nice address starting with their name:
//! 1**bob**YxBPjZWRPbVo35aSwci1u5Zmq8P6J2jpa4kkudBZMqE.
//!
//! **Note**: While `Bob`, having a short name (3 chars), got a result rather quickly, it will take
//! much longer for `Alice` who has a much longer name, thus the chances to generate a random
//! address that contains the chain `alice` will be much smaller.

use clap::Parser;
use sc_cli::{
	Error, GenerateCmd, GenerateNodeKeyCmd, InspectKeyCmd, InspectNodeKeyCmd, SignCmd, VanityCmd,
	VerifyCmd,
};

#[derive(Debug, Parser)]
#[command(
	name = "subkey",
	author = "Parity Team <admin@parity.io>",
	about = "Utility for generating and restoring with Substrate keys",
	version
)]
pub enum Subkey {
	/// Generate a random node key, write it to a file or stdout and write the
	/// corresponding peer-id to stderr
	GenerateNodeKey(GenerateNodeKeyCmd),

	/// Generate a random account
	Generate(GenerateCmd),

	/// Gets a public key and a SS58 address from the provided Secret URI
	Inspect(InspectKeyCmd),

	/// Load a node key from a file or stdin and print the corresponding peer-id
	InspectNodeKey(InspectNodeKeyCmd),

	/// Sign a message, with a given (secret) key.
	Sign(SignCmd),

	/// Generate a seed that provides a vanity address.
	Vanity(VanityCmd),

	/// Verify a signature for a message, provided on STDIN, with a given (public or secret) key.
	Verify(VerifyCmd),
}

/// Run the subkey command, given the appropriate runtime.
pub fn run() -> Result<(), Error> {
	match Subkey::parse() {
		Subkey::GenerateNodeKey(cmd) => cmd.run(),
		Subkey::Generate(cmd) => cmd.run(),
		Subkey::Inspect(cmd) => cmd.run(),
		Subkey::InspectNodeKey(cmd) => cmd.run(),
		Subkey::Vanity(cmd) => cmd.run(),
		Subkey::Verify(cmd) => cmd.run(),
		Subkey::Sign(cmd) => cmd.run(),
	}
}
