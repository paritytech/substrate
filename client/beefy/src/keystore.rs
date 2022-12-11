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

		let msg = keccak_256(message);
		let public = public.as_ref();

		let sig = SyncCryptoStore::bls_sign(&*store, KEY_TYPE, public, &msg)
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
	use sp_core::{ecdsa, bls, keccak_256, Pair};
        use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr, CryptoStore};
        use sp_application_crypto::Wraps;

	use beefy_primitives::{ecdsa_crypto, KEY_TYPE};
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

    pub(crate) trait PrehashedSigner : Pair {
	fn sign_prehashed(&self, hashed_message : &[u8; 32]) -> Self::Signature;
    }

 
    pub(crate) trait  GenericKeyring<TKeyPair> where
        TKeyPair: Clone + Sync + Send + From<Keyring> + Pair + PrehashedSigner,
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
        TKeyPair: Clone + Sync + Send + From<Keyring> + Pair + PrehashedSigner,
    {
 	// type Signature = ecdsa_crypto::Signature;
	// type Public = ecdsa_crypto::Public;
        // type KeyPair = ecdsa_crypto::Pair;
	
	/// Sign `msg`.
	fn sign(self, msg: &[u8]) -> TKeyPair::Signature {
	    let msg = keccak_256(msg);
	    TKeyPair::from(self).sign_prehashed(&msg).into()
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
    impl PrehashedSigner for ecdsa_crypto::Pair
    {
	fn sign_prehashed(&self, hashed_message : &[u8; 32]) -> Self::Signature {
	    self.as_inner_ref().sign_prehashed(hashed_message).into()
	}

    }
    

    impl From<Keyring> for ecdsa_crypto::Pair
    {
	fn from(k: Keyring) -> Self {
	    <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::pair(k)
	}
    }

    impl From<Keyring> for ecdsa::Pair {
	fn from(k: Keyring) -> Self {
	    <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::pair(k).into()
	}
    }

    fn keystore() -> SyncCryptoStorePtr {
	Arc::new(LocalKeystore::in_memory())
    }

    //Auxiliray tairt for ECDSAnBLS
    type ECDSAnBLSPair = (ecdsa_crypto::Pair, bls_crypto::Pair);

    impl CryptoType for ECDSAnBLSPair { }

    impl Pair for ECDSAnBLSPair {
	type Public = ;
	type Seed = Seed;
	type Signature = Signature;
	type DeriveError = DeriveError;

	/// Generate new secure (random) key pair and provide the recovery phrase.
	///
	/// You can recover the same key later with `from_phrase`.
	#[cfg(feature = "std")]
	fn generate_with_phrase(password: Option<&str>) -> (Pair, String, Seed) {
		let mnemonic = Mnemonic::new(MnemonicType::Words12, Language::English);
		let phrase = mnemonic.phrase();
		let (pair, seed) = Self::from_phrase(phrase, password)
			.expect("All phrases generated by Mnemonic are valid; qed");
		(pair, phrase.to_owned(), seed)
	}

	/// Generate key pair from given recovery phrase and password.
	#[cfg(feature = "std")]
	fn from_phrase(
		phrase: &str,
		password: Option<&str>,
	) -> Result<(Pair, Seed), SecretStringError> {
		let big_seed = seed_from_entropy(
			Mnemonic::from_phrase(phrase, Language::English)
				.map_err(|_| SecretStringError::InvalidPhrase)?
				.entropy(),
			password.unwrap_or(""),
		)
		.map_err(|_| SecretStringError::InvalidSeed)?;
		let mut seed = Seed::default();
		seed.copy_from_slice(&big_seed[0..32]);
		Self::from_seed_slice(&big_seed[0..32]).map(|x| (x, seed))
	}

	/// Make a new key pair from secret seed material.
	///
	/// You should never need to use this; generate(), generate_with_phrase
	fn from_seed(seed: &Seed) -> Pair {
		Self::from_seed_slice(&seed[..]).expect("seed has valid length; qed")
	}

	/// Make a new key pair from secret seed material. The slice must be 32 bytes long or it
	/// will return `None`.
	///
	/// You should never need to use this; generate(), generate_with_phrase
	fn from_seed_slice(seed_slice: &[u8]) -> Result<Pair, SecretStringError> {
        if seed_slice.len() != BLS377::SECRET_KEY_SIZE {
            return Err(SecretStringError::InvalidSeedLength);
        }        
		let secret = bls_like::SecretKey::from_seed(seed_slice);
		let public = secret.into_public();
		Ok(Pair(bls_like::Keypair { secret, public }))
	}

	/// Derive a child key from a series of given junctions.
	fn derive<Iter: Iterator<Item = DeriveJunction>>(
		&self,
		path: Iter,
		_seed: Option<Seed>,
	) -> Result<(Pair, Option<Seed>), DeriveError> {
		let mut acc = self.0.secret.to_bytes();
		for j in path {
			match j {
				DeriveJunction::Soft(_cc) => return Err(DeriveError::SoftKeyInPath),
				DeriveJunction::Hard(cc) => acc = derive_hard_junction(&acc, &cc),
			}
		}
		Ok((Self::from_seed(&acc), Some(acc)))
	}

	/// Get the public key.
	fn public(&self) -> Public {
		let mut r = [0u8; BLS377::PUBLICKEY_SERIALIZED_SIZE];
		let pk = self.0.public.to_bytes();
		r.copy_from_slice(pk.as_slice());
		Public(r)
	}

	/// Sign a message.
	fn sign(&self, message: &[u8]) -> Signature {
		let mut mutable_self = self.clone();
		let r = mutable_self.0.sign(Message::new(b"", message)).to_bytes();
		Signature::from_raw(r)
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	fn verify<M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: &Self::Public) -> bool {
		Self::verify_weak(&sig.0[..], message.as_ref(), pubkey)
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	///
	/// This doesn't use the type system to ensure that `sig` and `pubkey` are the correct
	/// size. Use it only if you're coming from byte buffers and need the speed.
	fn verify_weak<P: AsRef<[u8]>, M: AsRef<[u8]>>(sig: &[u8], message: M, pubkey: P) -> bool {
        let pubkey_array : [u8; BLS377::PUBLICKEY_SERIALIZED_SIZE]  = match pubkey.as_ref().try_into() {
			Ok(pk) => pk,
			Err(_) => return false,
        };        
		let public_key = match bls_like::PublicKey::<BLS377>::from_bytes(&pubkey_array) {
			Ok(pk) => pk,
			Err(_) => return false,
		};
        
		let sig_array  = match sig.try_into() {
			Ok(s) => s,
			Err(_) => return false,
		};
		let sig = match bls_like::Signature::from_bytes(sig_array) {
			Ok(s) => s,
			Err(_) => return false,
		};

		sig.verify(Message::new(b"", message.as_ref()), &public_key)
	}

	/// Return a vec filled with raw data.
	fn to_raw_vec(&self) -> Vec<u8> {
		self.seed().to_vec()
	}

    }
    #[test]
    fn verify_should_work() {
		let msg = keccak_256(b"I am Alice!");
		let sig = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::sign(Keyring::Alice, b"I am Alice!");

		assert!(ecdsa::Pair::verify_prehashed(
			&sig.clone().into(),
			&msg,
			&<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::public(Keyring::Alice).into(),
		));

		// different public key -> fail
		assert!(!ecdsa::Pair::verify_prehashed(
			&sig.clone().into(),
			&msg,
			&<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::public(Keyring::Bob).into(),
		));

		let msg = keccak_256(b"I am not Alice!");

		// different msg -> fail
		assert!(
			!ecdsa::Pair::verify_prehashed(&sig.into(), &msg, &<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::public(Keyring::Alice).into(),)
		);
	}

	#[test]
	fn pair_works() {
		let want = ecdsa_crypto::Pair::from_string("//Alice", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::pair(Keyring::Alice).to_raw_vec();
		assert_eq!(want, got);

		let want = ecdsa_crypto::Pair::from_string("//Bob", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::pair(Keyring::Bob).to_raw_vec();
		assert_eq!(want, got);

		let want = ecdsa_crypto::Pair::from_string("//Charlie", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::pair(Keyring::Charlie).to_raw_vec();
		assert_eq!(want, got);

		let want = ecdsa_crypto::Pair::from_string("//Dave", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::pair(Keyring::Dave).to_raw_vec();
		assert_eq!(want, got);

		let want = ecdsa_crypto::Pair::from_string("//Eve", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::pair(Keyring::Eve).to_raw_vec();
		assert_eq!(want, got);

		let want = ecdsa_crypto::Pair::from_string("//Ferdie", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::pair(Keyring::Ferdie).to_raw_vec();
		assert_eq!(want, got);

		let want = ecdsa_crypto::Pair::from_string("//One", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::pair(Keyring::One).to_raw_vec();
		assert_eq!(want, got);

		let want = ecdsa_crypto::Pair::from_string("//Two", None).expect("Pair failed").to_raw_vec();
		let got = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::pair(Keyring::Two).to_raw_vec();
		assert_eq!(want, got);
	}

	#[test]
	fn authority_id_works() {
		let store = keystore();

		let alice: ecdsa_crypto::Public =
			SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::to_seed(Keyring::Alice)))
				.ok()
				.unwrap()
				.into();

		let bob = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::public(Keyring::Bob);
		let charlie = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::public(Keyring::Charlie);

		let store: BeefyECDSAKeystore = BeefyECDSAKeystore::new(store);

		let mut keys = vec![bob, charlie];

		let id = store.authority_id(keys.as_slice());
		assert!(id.is_none());

		keys.push(alice.clone());

		let id = store.authority_id(keys.as_slice()).unwrap();
		assert_eq!(id, alice);
	}
    
	#[test]
	fn sign_works() {
		let store = keystore();

		let alice: ecdsa_crypto::Public =
			SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::to_seed(Keyring::Alice)))
				.ok()
				.unwrap()
				.into();

		let store = BeefyECDSAKeystore::new(store);

		let msg = b"are you involved or commited?";

		let sig1 = store.sign(&alice, msg).unwrap();
		let sig2 = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::sign(Keyring::Alice,msg);

		assert_eq!(sig1, sig2);
	}

	#[test]
	fn sign_error() {
		let store = keystore();

		let _ =
			SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::to_seed(Keyring::Bob)))
				.ok()
				.unwrap();

		let store = BeefyECDSAKeystore::new(store);

		let alice = <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::public(Keyring::Alice);

		let msg = b"are you involved or commited?";
		let sig = store.sign(&alice, msg).err().unwrap();
		let err = Error::Signature("ecdsa_sign_prehashed() failed".to_string());

		assert_eq!(sig, err);
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

	#[test]
	fn verify_works() {
		let store = keystore();

		let alice: ecdsa_crypto::Public =
			SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&<Keyring as GenericKeyring<ecdsa_crypto::Pair>>::to_seed(Keyring::Alice)))
				.ok()
				.unwrap()
				.into();

		let store = BeefyECDSAKeystore::new(store);

		// `msg` and `sig` match
		let msg = b"are you involved or commited?";
		let sig = store.sign(&alice, msg).unwrap();
		assert!(BeefyECDSAKeystore::verify(&alice, &sig, msg));

		// `msg and `sig` don't match
		let msg = b"you are just involved";
		assert!(!BeefyECDSAKeystore::verify(&alice, &sig, msg));
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
