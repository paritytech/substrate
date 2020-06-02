// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

use super::{SignCmd, VanityCmd};
use structopt::StructOpt;


#[test]
fn sign() {
	let seed = "0xad1fb77243b536b90cfe5f0d351ab1b1ac40e3890b41dc64f766ee56340cfca5";

	let sign = SignCmd::from_iter(&["sign", "--suri", seed, "--message", &seed[2..], "--password", "12345"]);
	assert!(sign.run().is_ok());
}

#[test]
fn vanity() {
	let vanity = VanityCmd::from_iter(&["vanity", "--number", "1", "--pattern", "j"]);
	assert!(vanity.run().is_ok());
}
