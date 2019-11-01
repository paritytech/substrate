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
	/// No seed matching the give account
	NoAccount,
	/// sr only accept hard derive
	SoftNotSupport,
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
/// the derive function will derive the 'keypair' in hardware and return the public
/// when sign function required after derive
/// the device will sign the message with derived key
	fn derive_public(&self, path: &[DeriveJunction]) -> Result<Public> {
		let mut pk: [u8; 32] = [0u8; 32];
		let mut vec = Vec::new();
		for j in path {
			match j {
// the soft derive not supported yet because in the neccessary 'fn derive_secret_key' schnorrkel
// ```
// let mut nonce = [0u8; 32];
// t.witness_bytes(b"HDKD-nonce", &mut nonce, &[&self.secret.nonce, &self.secret.to_bytes() as &[u8]]);
// (SecretKey {
//    key: self.secret.key + scalar,
//    nonce,
//}, chaincode)
// ```
// the witness_bytes requie rand_hack which panic("Attempted to use functionality that requires system randomness")
// because the CortexM3 could not fit the rand crate
//
// Jeff mentions the path and cc has  misissue in https://github.com/paritytech/substrate/pull/3777 and
// https://github.com/paritytech/substrate/issues/3396
// the one should pass to device is path and the device has chaincode inside
// one more thing is the HDKD wallet actually decide if it is harden by data in path, the highest bit is 1
// So when soft derive fixed, the hehavior will seem werid again here for just passing path to device
				DeriveJunction::Soft(_path) => return Err(Error::SoftNotSupport),
				DeriveJunction::Hard(path) => vec.push(path),
			}
		}
		let rv = wk_getpub(&mut pk, &vec);
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
	fn sign(&self, path: &[DeriveJunction], message: &[u8]) -> Result<Signature> {
		let mut sig: [u8; 64] = [0u8; 64];
		let mut vec = Vec::new();
		for j in path {
			match j {
				DeriveJunction::Soft(_path) => return Err(Error::SoftNotSupport),
				DeriveJunction::Hard(path) => vec.push(path),
			}
		}
		let rv = wk_sign(message, &mut sig, &vec);
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
