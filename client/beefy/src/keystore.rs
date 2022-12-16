// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use sp_application_crypto::RuntimeAppPublic;
use sp_core::keccak_256;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
use sp_runtime::traits::Keccak256;

use log::warn;

use beefy_primitives::{
	ecdsa_crypto::{Public as ECDSAPublic, Signature as ECDSASignature},
        bls_crypto::{Public as BLSPublic, Signature as BLSSignature},
        BeefyVerify,
	KEY_TYPE,
};

use codec::{Decode, Encode};
use core::fmt::Debug;
	
use crate::error;

use sp_core::bls::Pair as BLSPair;
use sp_application_crypto::Pair as app_crypto_Pair;
/// A BEEFY specific keystore implemented as a `Newtype`. This is basically a
/// wrapper around [`sp_keystore::SyncCryptoStore`] and allows to customize
/// common cryptographic functionality.
pub  trait BeefyKeystore<AuthorityId, TSignature> : From<Option<SyncCryptoStorePtr>> + Sync + Send where
	AuthorityId: Encode + Decode + Debug + Ord + Sync + Send,
	TSignature:  Encode + Decode + Debug + Clone + Sync + Send,
{
	type Public : Encode + Decode + Debug + From<AuthorityId> + Into<AuthorityId>;

	fn new(keystore: SyncCryptoStorePtr) -> Self;
	
    fn authority_id(&self, keys: &[AuthorityId]) -> Option<Self::Public>;

	fn sign(&self, public: &Self::Public, message: &[u8]) -> Result<TSignature,  error::Error>;

	fn public_keys(&self) -> Result<Vec<Self::Public>, error::Error>;

	fn authority_ids(&self) -> Result<Vec<AuthorityId>, error::Error>;

	fn verify(public: &Self::Public, sig: &TSignature, message: &[u8]) -> bool;

	fn authority_id_to_public_key(auth_id: &AuthorityId) -> Result<Self::Public,  error::Error>;

}

pub struct BeefyECDSAKeystore (Option<SyncCryptoStorePtr>);

pub struct BeefyBLSKeystore(Option<SyncCryptoStorePtr>);

pub struct BeefyBLSnECDSAKeystore(Option<SyncCryptoStorePtr>);

impl BeefyKeystore<ECDSAPublic,ECDSASignature> for  BeefyECDSAKeystore
{
	type Public = ECDSAPublic;
	
	fn new(keystore: SyncCryptoStorePtr) -> Self {	
		Self(Some(keystore))
	}

	/// Check if the keystore contains a private key for one of the public keys
	/// contained in `keys`. A public key with a matching private key is known
	/// as a local authority id.
	///
	/// Return the public key for which we also do have a private key. If no
	/// matching private key is found, `None` will be returned.
	fn authority_id(&self, keys: &[ECDSAPublic]) -> Option<Self::Public> {
		let store = self.0.clone()?;

		// we do check for multiple private keys as a key store sanity check.
		let public: Vec<Self::Public> = keys
			.iter()
			.filter(|k| SyncCryptoStore::has_keys(&*store, &[(k.to_raw_vec(), KEY_TYPE)]))
			.cloned()
			.collect();

		if public.len() > 1 {
			warn!(target: "beefy", "🥩 Multiple private keys found for: {:?} ({})", public, public.len());
		}

		public.get(0).cloned()
	}

	/// Sign `message` with the `public` key.
	///
	/// Note that `message` usually will be pre-hashed before being signed.
	///
	/// Return the message signature or an error in case of failure.
	fn sign(&self, public: &Self::Public, message: &[u8]) -> Result<ECDSASignature,  error::Error> {
		let store = self.0.clone().ok_or_else(|| error::Error::Keystore("no Keystore".into()))?;

		let msg = keccak_256(message);
		let public = public.as_ref();

		let sig = SyncCryptoStore::ecdsa_sign_prehashed(&*store, KEY_TYPE, public, &msg)
			.map_err(|e| error::Error::Keystore(e.to_string()))?
			.ok_or_else(|| error::Error::Signature("ecdsa_sign_prehashed() failed".to_string()))?;

		// check that `sig` has the expected result type
		let sig = sig.clone().try_into().map_err(|_| {
			error::Error::Signature(format!("invalid signature {:?} for key {:?}", sig, public))
		})?;

		Ok(sig)
	}

	/// Returns a vector of [`beefy_primitives::ecdsa_crypto::Public`] keys which are currently supported
	/// (i.e. found in the keystore).
	fn public_keys(&self) -> Result<Vec<Self::Public>, error::Error> {
		let store = self.0.clone().ok_or_else(|| error::Error::Keystore("no Keystore".into()))?;

		let pk: Vec<Self::Public> = SyncCryptoStore::ecdsa_public_keys(&*store, KEY_TYPE)
			.drain(..)
			.map(Self::Public::from)
			.collect();

		Ok(pk)
	}


	/// Returns a vector of [`beefy_primitives::ecdsa_crypto::Public`] keys which are currently supported
	/// (i.e. found in the keystore).
	fn authority_ids(&self) -> Result<Vec<ECDSAPublic>, error::Error> {
		self.public_keys()
	}
		
	/// Use the `public` key to verify that `sig` is a valid signature for `message`.
	///

	fn verify(public: &Self::Public, sig: &ECDSASignature, message: &[u8]) -> bool {
	    BeefyVerify::<Keccak256>::verify(sig, message, public)
	}

	fn authority_id_to_public_key(auth_id: &ECDSAPublic) -> Result<Self::Public,  error::Error> {
		Ok((*auth_id).clone())
	}
}

//Implement BLSKeyStore
impl BeefyKeystore<BLSPublic, BLSSignature> for  BeefyBLSKeystore
{	
	type Public = BLSPublic;

	fn new(keystore: SyncCryptoStorePtr) -> Self {	
		Self(Some(keystore))
	}
    
	/// Check if the keystore contains a private key for one of the public keys
	/// contained in `keys`. A public key with a matching private key is known
	/// as a local authority id.
	///
	/// Return the public key for which we also do have a private key. If no
	/// matching private key is found, `None` will be returned.
	fn authority_id(&self, keys: &[BLSPublic]) -> Option<Self::Public> {
		let store = self.0.clone()?;

		// we do check for multiple private keys as a key store sanity check.
		let public: Vec<Self::Public> = keys
			.iter()
			.filter(|k| SyncCryptoStore::has_keys(&*store, &[(k.to_raw_vec(), KEY_TYPE)]))
			.cloned()
			.collect();

		if public.len() > 1 {
			warn!(target: "beefy", "🥩 Multiple private keys found for: {:?} ({})", public, public.len());
		}

		public.get(0).cloned()
	}
	
	/// Sign `message` with the `public` key.
	///
	/// Note that `message` usually will be pre-hashed before being signed.
	///
	/// Return the message signature or an error in case of failure.
	fn sign(&self, public: &Self::Public, message: &[u8]) -> Result<BLSSignature,  error::Error> {
		let store = self.0.clone().ok_or_else(|| error::Error::Keystore("no Keystore".into()))?;

		let public = public.as_ref();

		let sig = SyncCryptoStore::bls_sign(&*store, KEY_TYPE, public, &message)
			.map_err(|e| error::Error::Keystore(e.to_string()))?
			.ok_or_else(|| error::Error::Signature("ecdsa_sign_prehashed() failed".to_string()))?;

		// check that `sig` has the expected result type
		let sig = sig.clone().try_into().map_err(|_| {
			error::Error::Signature(format!("invalid signature {:?} for key {:?}", sig, public))
		})?;

		Ok(sig)
	}

	/// Returns a vector of [`beefy_primitives::bls_crypto::Public`] keys which are currently supported
	/// (i.e. found in the keystore).
	fn public_keys(&self) -> Result<Vec<Self::Public>, error::Error> {
		let store = self.0.clone().ok_or_else(|| error::Error::Keystore("no Keystore".into()))?;

		let pk: Vec<Self::Public> = SyncCryptoStore::bls_public_keys(&*store, KEY_TYPE)
			.drain(..)
			.map(Self::Public::from)
			.collect();

		Ok(pk)
	}

	/// Returns a vector of [`beefy_primitives::bls_crypto::Public`] keys which are currently supported
	/// (i.e. found in the keystore).
	fn authority_ids(&self) -> Result<Vec<BLSPublic>, error::Error> {
		self.public_keys()
	}

	/// Use the `public` key to verify that `sig` is a valid signature for `message`.
	///
	/// Return `true` if the signature is authentic, `false` otherwise.
	fn verify(public: &Self::Public, sig: &BLSSignature, message: &[u8]) -> bool {
		let sig = sig.as_ref();
		let public = public.as_ref();

	    println!("{:?}: {}",message, sp_core::bls::Pair::verify(sig, &message, public));
	    sp_core::bls::Pair::verify(sig, &message, public)
	}

	fn authority_id_to_public_key(auth_id: &BLSPublic) -> Result<Self::Public,  error::Error> {
		Ok((*auth_id).clone())
	}

}

impl BeefyBLSnECDSAKeystore {
    fn both(&self) -> (BeefyECDSAKeystore, BeefyBLSKeystore) {
            ( BeefyECDSAKeystore(self.0.clone()), BeefyBLSKeystore(self.0.clone()))
    }
}

impl BeefyKeystore<(ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature)> for BeefyBLSnECDSAKeystore
{	
	fn new(keystore: SyncCryptoStorePtr) -> Self {	
		Self(Some(keystore))
	}

	type Public = (ECDSAPublic,BLSPublic);
	/// Check if the keystore contains a private key for one of the public keys
	/// contained in `keys`. A public key with a matching private key is known
	/// as a local authority id.
	///
	/// Return the public key for which we also do have a private key. If no
	/// matching private key is found, `None` will be returned.
	fn authority_id(&self, keys: &[(ECDSAPublic,BLSPublic)]) -> Option<Self::Public> {
		let (ecdsa_pubkeys, bls_pubkeys): (Vec<ECDSAPublic>, Vec<BLSPublic>) = keys.iter().cloned().unzip();
		let own_ecdsa_key = self.both().0.authority_id(&ecdsa_pubkeys);
		let own_bls_key  = self.both().1.authority_id(&bls_pubkeys); 
		if own_ecdsa_key == None || own_bls_key == None {
			None
		} else {
			Some((own_ecdsa_key.unwrap(), own_bls_key.unwrap()))
		}
	}

	fn sign(&self, public: &Self::Public, message: &[u8]) -> Result<(ECDSASignature,BLSSignature),  error::Error> {
		let bls_n_ecdsa = self.both();
		match (bls_n_ecdsa.0.sign(&public.0, message), bls_n_ecdsa.1.sign(&public.1, message)) {
			(Ok(ecdsa_sign),Ok(bls_sign))=> Ok((ecdsa_sign, bls_sign)),
			_ => Err(error::Error::Signature(format!("could not sign with both bls and ecdsa keys")))
		}
	}
								      
	fn public_keys(&self) -> Result<Vec<Self::Public>, error::Error> {
		let store = self.0.clone().ok_or_else(|| error::Error::Keystore("no Keystore".into()))?;

		let bls_n_ecdsa = self.both();
		let pk  : Vec<Self::Public> = bls_n_ecdsa.0.public_keys()?.into_iter().zip(bls_n_ecdsa.1.public_keys()?.into_iter()).collect();

		Ok(pk)

	}

	/// Returns a vector of [`(beefy_primitives::ecdsa_crypto::Public, beefy_primitives::bls_crypto::Public)`] keys which are currently supported
	/// (i.e. found in the keystore).
	fn authority_ids(&self) -> Result<Vec<(ECDSAPublic,BLSPublic)>, error::Error> {
		self.public_keys()
	}

	fn verify(public: &Self::Public, sig: &(ECDSASignature,BLSSignature), message: &[u8]) -> bool {
		match (BeefyECDSAKeystore::verify(&public.0, &sig.0, message),
		       BeefyBLSKeystore::verify(&public.1, &sig.1, message)) {
			(true, true) => true,
			_ => false
		}
	}

	fn authority_id_to_public_key(auth_id: &(ECDSAPublic,BLSPublic)) -> Result<Self::Public,  error::Error> {
		Ok((*auth_id).clone())
	}

}
    
macro_rules! impl_from_cryptostore_for_keystore {
    ($keystore:tt) => {
	    impl From<Option<SyncCryptoStorePtr>> for $keystore {
		    fn from(store: Option<SyncCryptoStorePtr>) -> $keystore {
			    $keystore(store)
		    }
	    }
    }
}

impl_from_cryptostore_for_keystore!(BeefyECDSAKeystore);
impl_from_cryptostore_for_keystore!(BeefyBLSKeystore);
impl_from_cryptostore_for_keystore!(BeefyBLSnECDSAKeystore);

#[cfg(test)]
pub mod tests {
	use std::sync::Arc;

	use sc_keystore::LocalKeystore;
	use sp_core::{ecdsa, bls, keccak_256, Pair, crypto::{SecretStringError}};
        use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr, CryptoStore};
        use sp_application_crypto::Wraps;

	use beefy_primitives::{ecdsa_crypto, bls_crypto, KEY_TYPE};
        use sp_runtime::testing::TestSignature;

        use super::{BeefyKeystore, BeefyECDSAKeystore, BeefyBLSnECDSAKeystore, ECDSAPublic, ECDSASignature, BLSPublic, BLSSignature};
        use codec::{Decode, Encode};
        use core::fmt::Debug;
    	use std::marker::PhantomData;

	use crate::error::Error;

	/// Set of test accounts using [`beefy_primitives::crypto`] types.
	#[allow(missing_docs)]
	#[derive(Debug, Clone, Copy, PartialEq, Eq, strum::Display, strum::EnumIter)]
	pub(crate) enum Keyring
    {
		Alice,
		Bob,
		Charlie,
		Dave,
		Eve,
		Ferdie,
		One,
	    Two,
		
	}

    pub(crate) trait SimpleKeyPair : Clone + Sized + Sync + Send  {
        type Public: Clone + Encode + Decode + Debug + Ord + Sync + Send;
	    type Signature:  Clone + Encode + Decode + Debug + Clone + Sync + Send;

	fn generate_in_store(store: SyncCryptoStorePtr, owner: Keyring) -> Self::Public;
			     
	fn sign(&self, hashed_message : &[u8]) -> Self::Signature;

	fn public(&self) -> Self::Public;

 	fn verify(sig: &Self::Signature, hashed_message : &[u8], pubkey: Self::Public) -> bool;

        fn from_string(s: &str, password_override: Option<&str>) -> Result<Self, SecretStringError>;

      	/// Return a vec filled with raw data.
	fn to_raw_vec(&self) -> Vec<u8>;
    }

    pub(crate) trait  GenericKeyring<TKeyPair> where
        TKeyPair: SimpleKeyPair,
    {
	/// Sign `msg`.
	fn sign(self, msg: &[u8]) -> TKeyPair::Signature;

	/// Return key pair.
	fn pair(self) -> TKeyPair;

	/// Return public key.
	fn public(self) -> TKeyPair::Public;

	/// Return seed string.
	fn to_seed(self) -> String;

    }
	
    impl<TKeyPair> GenericKeyring<TKeyPair> for Keyring where
        TKeyPair: SimpleKeyPair,
    {	
	/// Sign `msg`.
	fn sign(self, msg: &[u8]) -> TKeyPair::Signature {
            let key_pair = <Keyring as GenericKeyring<TKeyPair>>::pair(self);
	    key_pair.sign(&msg).into()
	}

	/// Return key pair.
	fn pair(self) -> TKeyPair {
	    TKeyPair::from_string(<Keyring as GenericKeyring<TKeyPair>>::to_seed(self).as_str(), None).unwrap().into()
	}

	/// Return public key.
	fn public(self) -> TKeyPair::Public {
	    <Keyring as GenericKeyring<TKeyPair>>::pair(self).public()
	}

	/// Return seed string.
	fn to_seed(self) -> String {
	    format!("//{}", self)
	}

    }

    // Auxiliary traits for ECDSA
    impl SimpleKeyPair for ecdsa_crypto::Pair
    {
        type Public = ecdsa_crypto::Public;
        type Signature = ecdsa_crypto::Signature;

        fn generate_in_store(store: SyncCryptoStorePtr, owner: Keyring) -> Self::Public {
	    SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::to_seed(owner)))
		.ok()
		.unwrap()
		.into()
	}
			     
	fn sign(&self, message : &[u8]) -> Self::Signature {
	    let hashed_message = keccak_256(message);
	    self.as_inner_ref().sign_prehashed(&hashed_message).into()
	}

 	fn verify(sig: &<Self as SimpleKeyPair>::Signature, message : &[u8], pubkey: Self::Public) -> bool        {
	    let hashed_message = keccak_256(message);
	    ecdsa::Pair::verify_prehashed(sig.as_inner_ref(), &hashed_message, pubkey.as_inner_ref())		
	}

	fn public(&self) -> Self::Public {
            <ecdsa_crypto::Pair as sp_application_crypto::Pair>::public(self)
        }

        fn from_string(s: &str, password_override: Option<&str>) -> Result<Self, SecretStringError> {
            <ecdsa_crypto::Pair as sp_application_crypto::Pair>::from_string(s, password_override)
        }

        /// Return a vec filled with raw data.
	fn to_raw_vec(&self) -> Vec<u8> {
            <ecdsa_crypto::Pair as sp_application_crypto::Pair>::to_raw_vec(self)
        }

    }    

    fn keystore() -> SyncCryptoStorePtr {
	    Arc::new(LocalKeystore::in_memory())
    }

    /// Auxiliray tairt for ECDSAnBLS
    #[derive(Clone)]
    struct ECDSAnBLSPair (pub ecdsa_crypto::Pair, pub bls_crypto::Pair);

    /// implementing ECDSAnBLSPair as a simple key pair to be used in the test key ring
    impl SimpleKeyPair for ECDSAnBLSPair
    {
        type Public = (ECDSAPublic,BLSPublic);
        type Signature = (ECDSASignature,BLSSignature);

        fn generate_in_store(store: SyncCryptoStorePtr, owner: Keyring) -> Self::Public {
	    (SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::to_seed(owner)))
	     .ok()
	     .unwrap().into(), 
             SyncCryptoStore::bls_generate_new(&*store, KEY_TYPE, Some(&<Keyring as GenericKeyring<ECDSAnBLSPair>>::to_seed(owner)))
	     .ok()
	     .unwrap()
	     .into()
	    )
    
	}
        
	fn sign(&self, message : &[u8]) -> Self::Signature {
	    let hashed_message = keccak_256(message);
            (self.0.as_inner_ref().sign_prehashed(&hashed_message).into(), self.1.sign(message))
	}

 	fn verify(sig: &Self::Signature, message : &[u8], pubkey: Self::Public) -> bool {
	    let hashed_message = keccak_256(message);
	    ecdsa::Pair::verify_prehashed(&sig.0.as_inner_ref(), &hashed_message, &pubkey.0.as_inner_ref()) &&	
	    bls_crypto::Pair::verify(&sig.1, &message, &pubkey.1)		
	}
	
	fn public(&self) -> Self::Public {
            (<ecdsa_crypto::Pair as sp_application_crypto::Pair>::public(&self.0), <bls_crypto::Pair as sp_application_crypto::Pair>::public(&self.1))
        }

        fn from_string(s: &str, password_override: Option<&str>) -> Result<Self, SecretStringError> {
            let ecdsa_pair = <ecdsa_crypto::Pair as sp_application_crypto::Pair>::from_string(s, password_override)?;
            let bls_pair = <bls_crypto::Pair as sp_application_crypto::Pair>::from_string(s, password_override)?;
	        Ok(ECDSAnBLSPair(ecdsa_pair, bls_pair))
        }
	
        /// Return a vec filled with raw data.
	fn to_raw_vec(&self) -> Vec<u8> {
            <ecdsa_crypto::Pair as sp_application_crypto::Pair>::to_raw_vec(&self.0)
        }
        
    }

    fn pair_verify_should_work<TKeyPair: SimpleKeyPair>() {
	let msg = b"I am Alice!";
	let sig = <Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Alice, b"I am Alice!");

	assert!(TKeyPair::verify(
			&sig,
			&msg.as_slice(),
			<Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice),
	));

	// different public key -> fail
	assert!(!TKeyPair::verify(
	    &sig,
	    &msg.as_slice(),
	    <Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob).into(),
	));

	let msg = b"I am not Alice!";

	// different msg -> fail
	assert!(
	    !TKeyPair::verify(&sig, &msg.as_slice(), <Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice))
	);
	
    }
    
    #[test]
    fn pair_verify_should_work_ecdsa() {
	pair_verify_should_work::<ecdsa_crypto::Pair>();
    }

    #[test]
    fn pair_verify_should_work_ecdsa_n_bls() {
	pair_verify_should_work::<ECDSAnBLSPair>();
    }

    fn pair_works<TKeyPair>()
        where TKeyPair : SimpleKeyPair,
    {
		let want = TKeyPair::from_string("//Alice", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<TKeyPair>>::pair(Keyring::Alice).to_raw_vec();
		assert_eq!(want, got);

		let want = TKeyPair::from_string("//Bob", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<TKeyPair>>::pair(Keyring::Bob).to_raw_vec();
		assert_eq!(want, got);

		let want = TKeyPair::from_string("//Charlie", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<TKeyPair>>::pair(Keyring::Charlie).to_raw_vec();
		assert_eq!(want, got);

		let want = TKeyPair::from_string("//Dave", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<TKeyPair>>::pair(Keyring::Dave).to_raw_vec();
		assert_eq!(want, got);

		let want = TKeyPair::from_string("//Eve", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<TKeyPair>>::pair(Keyring::Eve).to_raw_vec();
		assert_eq!(want, got);

		let want = TKeyPair::from_string("//Ferdie", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<TKeyPair>>::pair(Keyring::Ferdie).to_raw_vec();
		assert_eq!(want, got);

		let want = TKeyPair::from_string("//One", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<TKeyPair>>::pair(Keyring::One).to_raw_vec();
		assert_eq!(want, got);

		let want = TKeyPair::from_string("//Two", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<TKeyPair>>::pair(Keyring::Two).to_raw_vec();
		assert_eq!(want, got);
	}

    #[test]
    fn ecdsa_pair_works(){
        pair_works::<ecdsa_crypto::Pair>();
    }

    #[test]
    fn ecdsa_n_bls_pair_works () {
         pair_works::<ECDSAnBLSPair>();
    }

    fn authority_id_works<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
    where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId>,
          TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>,
    	  AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send,
	      TSignature:  Encode + Decode + Debug + Clone + Sync + Send,

    {
	let store = keystore();

	TKeyPair::generate_in_store(store.clone(), Keyring::Alice);

	let alice: TKeyPair::Public = <Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice);
    
	let bob = <Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Bob);
	let charlie = <Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Charlie);

	let beefy_store: TBeefyKeystore = TBeefyKeystore::new(store);

	let mut keys = vec![bob, charlie];

	let id = beefy_store.authority_id(keys.as_slice());
	assert!(id.is_none());

	keys.push(alice.clone());

	let id = beefy_store.authority_id(keys.as_slice()).unwrap();
	assert_eq!(id, alice);
    }

    #[test]
    fn authority_id_works_for_ecdsa() {	     	        
	authority_id_works::<ecdsa_crypto::Pair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>();
    }

    #[test]
    fn authority_id_works_for_ecdsa_n_bls() {
	    authority_id_works::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>();
    }

    fn sign_works<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
        where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId>,
              TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>,
    	      AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send,
	      TSignature:  Encode + Decode + Debug + Clone + Sync + Send,
    {
	let store = keystore();

	TKeyPair::generate_in_store(store.clone(), Keyring::Alice);

	let alice = <Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice);

        let store: TBeefyKeystore = TBeefyKeystore::new(store);

	let msg = b"are you involved or commited?";

	let sig1 = store.sign(&alice, msg).unwrap();
	let sig2 = <Keyring as GenericKeyring<TKeyPair>>::sign(Keyring::Alice,msg);

	assert_eq!(sig1.encode(), sig2.encode());
    }

    #[test]
    fn sign_works_for_ecdsa() {	     	        
	sign_works::<ecdsa_crypto::Pair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>();
    }

    #[test]
    fn sign_works_for_ecdsa_n_bls() {
	    sign_works::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>();
    }

    fn sign_error<TKeyPair, AuthId, TSignature, TBeefyKeystore>(expected_error_message: &str)
    where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId>,
          TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>,
    	  AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send,
	  TSignature:  Encode + Decode + Debug + Clone + Sync + Send,
    {
	let store = keystore();

	TKeyPair::generate_in_store(store.clone(), Keyring::Bob);		

	let store: TBeefyKeystore = TBeefyKeystore::new(store);

	let alice = <Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice);

	let msg = b"are you involved or commited?";
	let sig = store.sign(&alice, msg).err().unwrap();
	let err = Error::Signature(expected_error_message.to_string());

	assert_eq!(sig, err);
    }

    #[test]
    fn sign_error_for_ecdsa() {	     	        
	sign_error::<ecdsa_crypto::Pair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>("ecdsa_sign_prehashed() failed");
    }

    #[test]
    fn sign_error_for_ecdsa_n_bls() {
	    sign_error::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>("could not sign with both bls and ecdsa keys");
    }
    

    #[test]
	fn sign_no_keystore() {
		//TODO: new can not generate keystore with None element
		//I also don't think we need that. so this test should go away.
		// let store : BeefyKeystore = None.into();

		// let alice = Keyring::Alice.public();
		// let msg = b"are you involved or commited";

		//let sig = store.sign(&alice, msg).err().unwrap();
		// let err = Error::Keystore("no Keystore".to_string());
		// assert_eq!(sig, err);
	}

    fn verify_works<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
    where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId>,
          TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>,
    	  AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send,
	  TSignature:  Encode + Decode + Debug + Clone + Sync + Send,
    {
	let store = keystore();

	TKeyPair::generate_in_store(store.clone(), Keyring::Alice);		

	let store: TBeefyKeystore = TBeefyKeystore::new(store);

	let alice = <Keyring as GenericKeyring<TKeyPair>>::public(Keyring::Alice);

	// `msg` and `sig` match
	let msg = b"are you involved or commited?";
	let sig = store.sign(&alice, msg).unwrap();
	assert!(TBeefyKeystore::verify(&alice, &sig, msg));

	// `msg and `sig` don't match
	let msg = b"you are just involved";
	assert!(!TBeefyKeystore::verify(&alice, &sig, msg));
	
    }

    #[test]
    fn verify_works_for_ecdsa() {	     	        
	verify_works::<ecdsa_crypto::Pair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>();
    }

    #[test]
    fn verify_works_for_ecdsa_n_bls() {
	    verify_works::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>();
   } 

    // Note that we use keys with and without a seed for this test.
    #[test]
    fn public_keys_works() {
	const TEST_TYPE: sp_application_crypto::KeyTypeId =
	    sp_application_crypto::KeyTypeId(*b"test");

	let store = keystore();

	let add_key = |key_type, seed: Option<&str>| {
	    SyncCryptoStore::ecdsa_generate_new(&*store, key_type, seed).unwrap()
	};

		// test keys
		let _ = add_key(TEST_TYPE, Some(<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::to_seed(Keyring::Alice).as_str()));
		let _ = add_key(TEST_TYPE, Some(<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::to_seed(Keyring::Bob).as_str()));

		let _ = add_key(TEST_TYPE, None);
		let _ = add_key(TEST_TYPE, None);

		// BEEFY keys
		let _ = add_key(KEY_TYPE, Some(<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::to_seed(Keyring::Dave).as_str()));
		let _ = add_key(KEY_TYPE, Some(<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::to_seed(Keyring::Eve).as_str()));

		let key1: ecdsa_crypto::Public = add_key(KEY_TYPE, None).into();
		let key2: ecdsa_crypto::Public = add_key(KEY_TYPE, None).into();

		let store = BeefyECDSAKeystore::new(store);

		let keys = store.public_keys().ok().unwrap();

		assert!(keys.len() == 4);
		assert!(keys.contains(&<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::public(Keyring::Dave)));
		assert!(keys.contains(&<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::public(Keyring::Eve)));
		assert!(keys.contains(&key1));
		assert!(keys.contains(&key2));
	}
}
