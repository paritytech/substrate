// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

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

//! # Authority discovery module.
//!
//! This module is used by the `core/authority-discovery` to retrieve the
//! current set of authorities, learn its own authority id as well as sign and
//! verify messages to and from other authorities.
//!
//! ## Dependencies
//!
//! This module depends on the [Im online module](../srml_im_online/index.html)
//! using its session key.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use app_crypto::RuntimeAppPublic;
use codec::{Decode, Encode};
use rstd::prelude::*;
use srml_support::{decl_module, decl_storage, StorageValue};

pub trait Trait: system::Trait + session::Trait {}

decl_storage! {
    trait Store for Module<T: Trait> as AuthorityDiscovery {
        /// The current set of keys that may issue a heartbeat.
        Keys get(keys) config(): Vec<im_online::AuthorityId>;
    }
}

decl_module! {
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
    }
}

impl<T: Trait> Module<T> {
    pub fn public_key() -> Option<im_online::AuthorityId> {
        let authorities = Keys::get();

        let local_keys = im_online::AuthorityId::all();

        let mut intersect: Vec<im_online::AuthorityId> = authorities
            .into_iter()
            .filter_map(|authority| {
                if local_keys.contains(&authority) {
                    Some(authority)
                } else {
                    None
                }
            })
            .collect();

        // TODO: We ignore all but the last one, should we care about all of them?
        intersect.pop()
    }

    pub fn authorities() -> Vec<im_online::AuthorityId> {
        Keys::get()
    }

    pub fn sign(payload: Vec<u8>) -> Option<Vec<u8>> {
        let pub_key = Module::<T>::public_key()?;

        pub_key.sign(&payload).map(|s| s.encode())
    }

    pub fn verify(
        payload: Vec<u8>,
        signature: Vec<u8>,
        public_key: im_online::AuthorityId,
    ) -> bool {
        let sig: Result<im_online::AuthoritySignature, _> = Decode::decode(&mut &signature[..]);

        match sig {
            Ok(sig) => public_key.verify(&payload, &sig),
            Err(_e) => false,
        }
    }
}

impl<T: Trait> session::OneSessionHandler<T::AccountId> for Module<T> {
    type Key = im_online::AuthorityId;

    fn on_new_session<'a, I: 'a>(_changed: bool, _validators: I, next_validators: I)
    where
        I: Iterator<Item = (&'a T::AccountId, im_online::AuthorityId)>,
    {
        // Remember who the authorities are for the new session.
        Keys::put(next_validators.map(|x| x.1).collect::<Vec<_>>());
    }

    fn on_disabled(_i: usize) {
        // ignore
    }
}
