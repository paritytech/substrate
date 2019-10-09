// Copyright (c) 2017-2019 Chester Li and extropies.com
// Copyright 2018-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate/subhd.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.
// See LICENSE for licensing information.
//
// Original author:
// - Chester Li<chester@lichester.com>

//! Rust bindings for Wookong hardware wallet.

use primitives::{
	sr25519::{self, Signature, Public, Pair}, crypto::{DeriveJunction, Pair as TraitPair}
};
use wookong_solo::{wk_getpub, wk_sign, wk_generate, wk_format, wk_import};

/// Error define
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Error {
	/// Device not connected.
	DeviceNotFound,
	/// Empty device; key must be generated or imported first.
	DeviceNotInit,
	/// General error of command.
	DeviceError,
}

/// Result type.
pub type Result<T> = std::result::Result<T, Error>;

/// Interface for the manager of a key.
pub trait Wallet {
	/// The keypair type.
	type Pair: TraitPair;
	/// Retrieve public key, if device is initialized.
	fn derive_public(&self, path: &[DeriveJunction]) -> Result<<Self::Pair as TraitPair>::Public>;
	/// Sign the message.
	fn sign(&self, path: &[DeriveJunction], message: &[u8]) -> Result<<Self::Pair as TraitPair>::Signature>;
	/// Generate keypair and return seed.
	fn generate(&self) -> Result<Self::Pair>;
	/// Import seed.
	fn import(&self, seed: &<Self::Pair as TraitPair>::Seed) -> Result<()>;
	/// Clear the device to empty.
	fn reset(&self) -> Result<()>;
}

impl<T: TraitPair> Wallet for T {
	type Pair = T;
	fn derive_public(&self, _: &[DeriveJunction]) -> Result<<Self::Pair as TraitPair>::Public> { Err(Error::DeviceNotFound) }
	fn sign(&self, _: &[DeriveJunction], _: &[u8]) -> Result<<Self::Pair as TraitPair>::Signature> { Err(Error::DeviceNotFound) }
	fn generate(&self) -> Result<Self::Pair> { Err(Error::DeviceNotFound) }
	fn import(&self, _: &<Self::Pair as TraitPair>::Seed) -> Result<()> { Err(Error::DeviceNotFound) }
	fn reset(&self) -> Result<()> { Err(Error::DeviceNotFound) }
}

/// Unit type representing the Wookong hardware wallet.
pub struct Wookong;

impl Wallet for Wookong {
	type Pair = sr25519::Pair;
	fn derive_public(&self, _path: &[DeriveJunction]) -> Result<Public> {
		// TODO: pass through _path and _password to mutate the key on the device accordingly.
		let mut pk: [u8; 32] = [0u8; 32];
		let rv = wk_getpub(&mut pk);
		if rv == 242 {
			return Err(Error::DeviceNotInit);
		} else if rv != 0 {
			return Err(Error::DeviceNotFound);
		} else if rv == 0 {
			Ok(sr25519::Public::from_raw(pk))
		} else {
			return Err(Error::DeviceError);
		}
	}
	fn sign(&self, _path: &[DeriveJunction], message: &[u8]) -> Result<Signature> {
		// TODO: pass through _path and _password to mutate the key on the device accordingly.
		let mut sig: [u8; 64] = [0u8; 64];
		let rv = wk_sign(message, &mut sig);
		if rv != 0 {
			return Err(Error::DeviceError);
		}
		Ok(sr25519::Signature::from_raw(sig))
	}
	fn generate(&self) -> Result<Pair> {
		let mut seed: [u8; 32] = [0u8; 32];
		let rv = wk_generate(&mut seed);
		if rv != 0 {
			return Err(Error::DeviceError);
		}
		Ok(Pair::from_seed(&seed))
	}
	fn reset(&self) -> Result<()> {
		let rv = wk_format();
		if rv != 0 {
			return Err(Error::DeviceError);
		}
		Ok(())
	}
	fn import(&self, seed: &<Pair as TraitPair>::Seed) -> Result<()> {
		let rv = wk_import(seed.as_ref());
		if rv != 0 {
			return Err(Error::DeviceError);
		}
		Ok(())
	}
}
