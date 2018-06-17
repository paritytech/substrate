// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

//! Predefined chains.

/// The chain specification (this should eventually be replaced by a more general JSON-based chain
/// specification).
#[derive(Clone, Debug)]
pub enum ChainSpec {
	/// Whatever the current runtime is, with just Alice as an auth.
	Development,
	/// Whatever the current runtime is, with simple Alice/Bob auths.
	LocalTestnet,
	/// The PoC-1 testnet.
	PoC1Testnet,
	/// The PoC-2 testnet.
	PoC2Testnet,
	/// Custom Genesis file.
	Custom(String),
}

impl<'a> From<&'a str> for ChainSpec {
	fn from(s: &'a str) -> Self {
		match s {
			"dev" => ChainSpec::Development,
			"local" => ChainSpec::LocalTestnet,
			"poc-1" => ChainSpec::PoC1Testnet,
			"poc-2" => ChainSpec::PoC2Testnet,
			s => ChainSpec::Custom(s.into()),
		}
	}
}

impl From<ChainSpec> for String {
	fn from(s: ChainSpec) -> String {
		match s {
			ChainSpec::Development => "dev".into(),
			ChainSpec::LocalTestnet => "local".into(),
			ChainSpec::PoC1Testnet => "poc-1".into(),
			ChainSpec::PoC2Testnet => "poc-2".into(),
			ChainSpec::Custom(f) => format!("custom ({})", f),
		}
	}
}

impl ::std::fmt::Display for ChainSpec {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		if let ChainSpec::Custom(n) = self {
			write!(f, "Custom ({})", n)
		} else {
			write!(f, "{}", match *self {
				ChainSpec::Development => "Development",
				ChainSpec::LocalTestnet => "Local Testnet",
				ChainSpec::PoC1Testnet => "PoC-1 Testnet",
				ChainSpec::PoC2Testnet => "PoC-2 Testnet",
				_ => unreachable!(),
			})
		}
	}
}
