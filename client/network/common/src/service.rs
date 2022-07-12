// This file is part of Substrate.
//
// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.
//
// If you read this, you are very thorough, congratulations.

pub use libp2p::{identity::error::SigningError, kad::record::Key as KademliaKey};
pub use signature::Signature;
use std::sync::Arc;

mod signature;

/// Signer with network identity
pub trait NetworkSigner {
	/// Signs the message with the `KeyPair` that defined the local `PeerId`.
	fn sign_with_local_identity(&self, msg: impl AsRef<[u8]>) -> Result<Signature, SigningError>;
}

impl<T> NetworkSigner for Arc<T>
where
	T: ?Sized,
	T: NetworkSigner,
{
	fn sign_with_local_identity(&self, msg: impl AsRef<[u8]>) -> Result<Signature, SigningError> {
		T::sign_with_local_identity(self, msg)
	}
}

/// Get value network provider.
pub trait NetworkKVProvider {
	/// Start getting a value from the DHT.
	fn get_value(&self, key: &KademliaKey);

	/// Start putting a value in the DHT.
	fn put_value(&self, key: KademliaKey, value: Vec<u8>);
}

impl<T> NetworkKVProvider for Arc<T>
where
	T: ?Sized,
	T: NetworkKVProvider,
{
	fn get_value(&self, key: &KademliaKey) {
		T::get_value(self, key)
	}

	fn put_value(&self, key: KademliaKey, value: Vec<u8>) {
		T::put_value(self, key, value)
	}
}
