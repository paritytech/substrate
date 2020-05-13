// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Runtime Modules shared primitive types.

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

// to allow benchmarking
#![cfg_attr(feature = "bench", feature(test))]
#[cfg(feature = "bench")] extern crate test;

#[doc(hidden)]
pub use codec;
#[cfg(feature = "std")]
#[doc(hidden)]
pub use serde;
#[doc(hidden)]
pub use sp_std;

#[doc(hidden)]
pub use paste;

#[doc(hidden)]
pub use sp_application_crypto as app_crypto;

#[cfg(feature = "std")]
pub use sp_core::storage::{Storage, StorageChild};

use sp_std::prelude::*;
use sp_std::convert::TryFrom;
use sp_core::{crypto::{self, Public}, ed25519, sr25519, ecdsa, hash::{H256, H512}};

use codec::{Encode, Decode};

pub mod curve;
pub mod generic;
pub mod offchain;
#[cfg(feature = "std")]
pub mod testing;
pub mod traits;
pub mod transaction_validity;
pub mod random_number_generator;
mod runtime_string;

pub use crate::runtime_string::*;

/// Re-export these since they're only "kind of" generic.
pub use generic::{DigestItem, Digest};

/// Re-export this since it's part of the API of this crate.
pub use sp_core::{TypeId, crypto::{key_types, KeyTypeId, CryptoType, CryptoTypeId, AccountId32}};
pub use sp_application_crypto::{RuntimeAppPublic, BoundToRuntimeAppPublic};

/// Re-export `RuntimeDebug`, to avoid dependency clutter.
pub use sp_core::RuntimeDebug;

/// Re-export top-level arithmetic stuff.
pub use sp_arithmetic::{
	Perquintill, Perbill, Permill, Percent, PerU16, Rational128, Fixed64, Fixed128,
	PerThing, traits::SaturatedConversion,
};
/// Re-export 128 bit helpers.
pub use sp_arithmetic::helpers_128bit;
/// Re-export big_uint stuff.
pub use sp_arithmetic::biguint;

pub use random_number_generator::RandomNumberGenerator;

/// An abstraction over justification for a block's validity under a consensus algorithm.
///
/// Essentially a finality proof. The exact formulation will vary between consensus
/// algorithms. In the case where there are multiple valid proofs, inclusion within
/// the block itself would allow swapping justifications to change the block's hash
/// (and thus fork the chain). Sending a `Justification` alongside a block instead
/// bypasses this problem.
pub type Justification = Vec<u8>;

use traits::{Verify, Lazy};

/// A module identifier. These are per module and should be stored in a registry somewhere.
#[derive(Clone, Copy, Eq, PartialEq, Encode, Decode)]
pub struct ModuleId(pub [u8; 8]);

impl TypeId for ModuleId {
	const TYPE_ID: [u8; 4] = *b"modl";
}

#[cfg(feature = "std")]
pub use serde::{Serialize, Deserialize, de::DeserializeOwned};
use crate::traits::IdentifyAccount;

/// Complex storage builder stuff.
#[cfg(feature = "std")]
pub trait BuildStorage {
	/// Build the storage out of this builder.
	fn build_storage(&self) -> Result<sp_core::storage::Storage, String> {
		let mut storage = Default::default();
		self.assimilate_storage(&mut storage)?;
		Ok(storage)
	}
	/// Assimilate the storage for this module into pre-existing overlays.
	fn assimilate_storage(
		&self,
		storage: &mut sp_core::storage::Storage,
	) -> Result<(), String>;
}

/// Something that can build the genesis storage of a module.
#[cfg(feature = "std")]
pub trait BuildModuleGenesisStorage<T, I>: Sized {
	/// Create the module genesis storage into the given `storage` and `child_storage`.
	fn build_module_genesis_storage(
		&self,
		storage: &mut sp_core::storage::Storage,
	) -> Result<(), String>;
}

#[cfg(feature = "std")]
impl BuildStorage for sp_core::storage::Storage {
	fn assimilate_storage(
		&self,
		storage: &mut sp_core::storage::Storage,
	)-> Result<(), String> {
		storage.top.extend(self.top.iter().map(|(k, v)| (k.clone(), v.clone())));
		for (k, other_map) in self.children_default.iter() {
			let k = k.clone();
			if let Some(map) = storage.children_default.get_mut(&k) {
				map.data.extend(other_map.data.iter().map(|(k, v)| (k.clone(), v.clone())));
				if !map.child_info.try_update(&other_map.child_info) {
					return Err("Incompatible child info update".to_string());
				}
			} else {
				storage.children_default.insert(k, other_map.clone());
			}
		}
		Ok(())
	}
}

#[cfg(feature = "std")]
impl BuildStorage for () {
	fn assimilate_storage(
		&self,
		_: &mut sp_core::storage::Storage,
	)-> Result<(), String> {
		Err("`assimilate_storage` not implemented for `()`".into())
	}
}

/// Consensus engine unique ID.
pub type ConsensusEngineId = [u8; 4];

/// Signature verify that can work with any known signature types..
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Eq, PartialEq, Clone, Encode, Decode, RuntimeDebug)]
pub enum MultiSignature {
	/// An Ed25519 signature.
	Ed25519(ed25519::Signature),
	/// An Sr25519 signature.
	Sr25519(sr25519::Signature),
	/// An ECDSA/SECP256k1 signature.
	Ecdsa(ecdsa::Signature),
}

impl From<ed25519::Signature> for MultiSignature {
	fn from(x: ed25519::Signature) -> Self {
		MultiSignature::Ed25519(x)
	}
}

impl TryFrom<MultiSignature> for ed25519::Signature {
	type Error = ();
	fn try_from(m: MultiSignature) -> Result<Self, Self::Error> {
		if let MultiSignature::Ed25519(x) = m { Ok(x) } else { Err(()) }
	}
}

impl From<sr25519::Signature> for MultiSignature {
	fn from(x: sr25519::Signature) -> Self {
		MultiSignature::Sr25519(x)
	}
}

impl TryFrom<MultiSignature> for sr25519::Signature {
	type Error = ();
	fn try_from(m: MultiSignature) -> Result<Self, Self::Error> {
		if let MultiSignature::Sr25519(x) = m { Ok(x) } else { Err(()) }
	}
}

impl From<ecdsa::Signature> for MultiSignature {
	fn from(x: ecdsa::Signature) -> Self {
		MultiSignature::Ecdsa(x)
	}
}

impl TryFrom<MultiSignature> for ecdsa::Signature {
	type Error = ();
	fn try_from(m: MultiSignature) -> Result<Self, Self::Error> {
		if let MultiSignature::Ecdsa(x) = m { Ok(x) } else { Err(()) }
	}
}

impl Default for MultiSignature {
	fn default() -> Self {
		MultiSignature::Ed25519(Default::default())
	}
}

/// Public key for any known crypto algorithm.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum MultiSigner {
	/// An Ed25519 identity.
	Ed25519(ed25519::Public),
	/// An Sr25519 identity.
	Sr25519(sr25519::Public),
	/// An SECP256k1/ECDSA identity (actually, the Blake2 hash of the compressed pub key).
	Ecdsa(ecdsa::Public),
}

impl Default for MultiSigner {
	fn default() -> Self {
		MultiSigner::Ed25519(Default::default())
	}
}

/// NOTE: This implementations is required by `SimpleAddressDeterminer`,
/// we convert the hash into some AccountId, it's fine to use any scheme.
impl<T: Into<H256>> crypto::UncheckedFrom<T> for MultiSigner {
	fn unchecked_from(x: T) -> Self {
		ed25519::Public::unchecked_from(x.into()).into()
	}
}

impl AsRef<[u8]> for MultiSigner {
	fn as_ref(&self) -> &[u8] {
		match *self {
			MultiSigner::Ed25519(ref who) => who.as_ref(),
			MultiSigner::Sr25519(ref who) => who.as_ref(),
			MultiSigner::Ecdsa(ref who) => who.as_ref(),
		}
	}
}

impl traits::IdentifyAccount for MultiSigner {
	type AccountId = AccountId32;
	fn into_account(self) -> AccountId32 {
		match self {
			MultiSigner::Ed25519(who) => <[u8; 32]>::from(who).into(),
			MultiSigner::Sr25519(who) => <[u8; 32]>::from(who).into(),
			MultiSigner::Ecdsa(who) => sp_io::hashing::blake2_256(&who.as_ref()[..]).into(),
		}
	}
}

impl From<ed25519::Public> for MultiSigner {
	fn from(x: ed25519::Public) -> Self {
		MultiSigner::Ed25519(x)
	}
}

impl TryFrom<MultiSigner> for ed25519::Public {
	type Error = ();
	fn try_from(m: MultiSigner) -> Result<Self, Self::Error> {
		if let MultiSigner::Ed25519(x) = m { Ok(x) } else { Err(()) }
	}
}

impl From<sr25519::Public> for MultiSigner {
	fn from(x: sr25519::Public) -> Self {
		MultiSigner::Sr25519(x)
	}
}

impl TryFrom<MultiSigner> for sr25519::Public {
	type Error = ();
	fn try_from(m: MultiSigner) -> Result<Self, Self::Error> {
		if let MultiSigner::Sr25519(x) = m { Ok(x) } else { Err(()) }
	}
}

impl From<ecdsa::Public> for MultiSigner {
	fn from(x: ecdsa::Public) -> Self {
		MultiSigner::Ecdsa(x)
	}
}

impl TryFrom<MultiSigner> for ecdsa::Public {
	type Error = ();
	fn try_from(m: MultiSigner) -> Result<Self, Self::Error> {
		if let MultiSigner::Ecdsa(x) = m { Ok(x) } else { Err(()) }
	}
}

#[cfg(feature = "std")]
impl std::fmt::Display for MultiSigner {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			MultiSigner::Ed25519(ref who) => write!(fmt, "ed25519: {}", who),
			MultiSigner::Sr25519(ref who) => write!(fmt, "sr25519: {}", who),
			MultiSigner::Ecdsa(ref who) => write!(fmt, "ecdsa: {}", who),
		}
	}
}

impl Verify for MultiSignature {
	type Signer = MultiSigner;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &AccountId32) -> bool {
		match (self, signer) {
			(MultiSignature::Ed25519(ref sig), who) => sig.verify(msg, &ed25519::Public::from_slice(who.as_ref())),
			(MultiSignature::Sr25519(ref sig), who) => sig.verify(msg, &sr25519::Public::from_slice(who.as_ref())),
			(MultiSignature::Ecdsa(ref sig), who) => {
				let m = sp_io::hashing::blake2_256(msg.get());
				match sp_io::crypto::secp256k1_ecdsa_recover_compressed(sig.as_ref(), &m) {
					Ok(pubkey) =>
						&sp_io::hashing::blake2_256(pubkey.as_ref())
							== <dyn AsRef<[u8; 32]>>::as_ref(who),
					_ => false,
				}
			}
		}
	}
}

/// Signature verify that can work with any known signature types..
#[derive(Eq, PartialEq, Clone, Default, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct AnySignature(H512);

impl Verify for AnySignature {
	type Signer = sr25519::Public;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &sr25519::Public) -> bool {
		let msg = msg.get();
		sr25519::Signature::try_from(self.0.as_fixed_bytes().as_ref())
			.map(|s| s.verify(msg, signer))
			.unwrap_or(false)
		|| ed25519::Signature::try_from(self.0.as_fixed_bytes().as_ref())
			.map(|s| s.verify(msg, &ed25519::Public::from_slice(signer.as_ref())))
			.unwrap_or(false)
	}
}

impl From<sr25519::Signature> for AnySignature {
	fn from(s: sr25519::Signature) -> Self {
		AnySignature(s.into())
	}
}

impl From<ed25519::Signature> for AnySignature {
	fn from(s: ed25519::Signature) -> Self {
		AnySignature(s.into())
	}
}

impl From<DispatchError> for DispatchOutcome {
	fn from(err: DispatchError) -> Self {
		Err(err)
	}
}

/// This is the legacy return type of `Dispatchable`. It is still exposed for compatibilty
/// reasons. The new return type is `DispatchResultWithInfo`.
/// FRAME runtimes should use frame_support::dispatch::DispatchResult
pub type DispatchResult = sp_std::result::Result<(), DispatchError>;

/// Return type of a `Dispatchable` which contains the `DispatchResult` and additional information
/// about the `Dispatchable` that is only known post dispatch.
pub type DispatchResultWithInfo<T> = sp_std::result::Result<T, DispatchErrorWithPostInfo<T>>;

/// Reason why a dispatch call failed
#[derive(Eq, PartialEq, Clone, Copy, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub enum DispatchError {
	/// Some error occurred.
	Other(#[codec(skip)] &'static str),
	/// Failed to lookup some data.
	CannotLookup,
	/// A bad origin.
	BadOrigin,
	/// A custom error in a module
	Module {
		/// Module index, matching the metadata module index
		index: u8,
		/// Module specific error value
		error: u8,
		/// Optional error message.
		#[codec(skip)]
		message: Option<&'static str>,
	},
}

/// Result of a `Dispatchable` which contains the `DispatchResult` and additional information
/// about the `Dispatchable` that is only known post dispatch.
#[derive(Eq, PartialEq, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub struct DispatchErrorWithPostInfo<Info> where
	Info: Eq + PartialEq + Clone + Copy + Encode + Decode + traits::Printable
{
	/// Addditional information about the `Dispatchable` which is only known post dispatch.
	pub post_info: Info,
	/// The actual `DispatchResult` indicating whether the dispatch was succesfull.
	pub error: DispatchError,
}

impl DispatchError {
	/// Return the same error but without the attached message.
	pub fn stripped(self) -> Self {
		match self {
			DispatchError::Module { index, error, message: Some(_) }
				=> DispatchError::Module { index, error, message: None },
			m => m,
		}
	}
}

impl<T, E> From<E> for DispatchErrorWithPostInfo<T> where
	T: Eq + PartialEq + Clone + Copy + Encode + Decode + traits::Printable + Default,
	E: Into<DispatchError>
{
	fn from(error: E) -> Self {
		Self {
			post_info: Default::default(),
			error: error.into(),
		}
	}
}

impl From<crate::traits::LookupError> for DispatchError {
	fn from(_: crate::traits::LookupError) -> Self {
		Self::CannotLookup
	}
}

impl From<crate::traits::BadOrigin> for DispatchError {
	fn from(_: crate::traits::BadOrigin) -> Self {
		Self::BadOrigin
	}
}

impl From<&'static str> for DispatchError {
	fn from(err: &'static str) -> DispatchError {
		DispatchError::Other(err)
	}
}

impl From<DispatchError> for &'static str {
	fn from(err: DispatchError) -> &'static str {
		match err {
			DispatchError::Other(msg) => msg,
			DispatchError::CannotLookup => "Can not lookup",
			DispatchError::BadOrigin => "Bad origin",
			DispatchError::Module { message, .. } => message.unwrap_or("Unknown module error"),
		}
	}
}

impl<T> From<DispatchErrorWithPostInfo<T>> for &'static str where
	T: Eq + PartialEq + Clone + Copy + Encode + Decode + traits::Printable
{
	fn from(err: DispatchErrorWithPostInfo<T>) -> &'static str {
		err.error.into()
	}
}

impl traits::Printable for DispatchError {
	fn print(&self) {
		"DispatchError".print();
		match self {
			Self::Other(err) => err.print(),
			Self::CannotLookup => "Can not lookup".print(),
			Self::BadOrigin => "Bad origin".print(),
			Self::Module { index, error, message } => {
				index.print();
				error.print();
				if let Some(msg) = message {
					msg.print();
				}
			}
		}
	}
}

impl<T> traits::Printable for DispatchErrorWithPostInfo<T> where
	T: Eq + PartialEq + Clone + Copy + Encode + Decode + traits::Printable
{
	fn print(&self) {
		self.error.print();
		"PostInfo: ".print();
		self.post_info.print();
	}
}

/// This type specifies the outcome of dispatching a call to a module.
///
/// In case of failure an error specific to the module is returned.
///
/// Failure of the module call dispatching doesn't invalidate the extrinsic and it is still included
/// in the block, therefore all state changes performed by the dispatched call are still persisted.
///
/// For example, if the dispatching of an extrinsic involves inclusion fee payment then these
/// changes are going to be preserved even if the call dispatched failed.
pub type DispatchOutcome = Result<(), DispatchError>;

/// The result of applying of an extrinsic.
///
/// This type is typically used in the context of `BlockBuilder` to signal that the extrinsic
/// in question cannot be included.
///
/// A block containing extrinsics that have a negative inclusion outcome is invalid. A negative
/// result can only occur during the block production, where such extrinsics are detected and
/// removed from the block that is being created and the transaction pool.
///
/// To rehash: every extrinsic in a valid block must return a positive `ApplyExtrinsicResult`.
///
/// Examples of reasons preventing inclusion in a block:
/// - More block weight is required to process the extrinsic than is left in the block being built.
///   This doesn't necessarily mean that the extrinsic is invalid, since it can still be
///   included in the next block if it has enough spare weight available.
/// - The sender doesn't have enough funds to pay the transaction inclusion fee. Including such
///   a transaction in the block doesn't make sense.
/// - The extrinsic supplied a bad signature. This transaction won't become valid ever.
pub type ApplyExtrinsicResult = Result<DispatchOutcome, transaction_validity::TransactionValidityError>;

/// Verify a signature on an encoded value in a lazy manner. This can be
/// an optimization if the signature scheme has an "unsigned" escape hash.
pub fn verify_encoded_lazy<V: Verify, T: codec::Encode>(
	sig: &V,
	item: &T,
	signer: &<V::Signer as IdentifyAccount>::AccountId
) -> bool {
	// The `Lazy<T>` trait expresses something like `X: FnMut<Output = for<'a> &'a T>`.
	// unfortunately this is a lifetime relationship that can't
	// be expressed without generic associated types, better unification of HRTBs in type position,
	// and some kind of integration into the Fn* traits.
	struct LazyEncode<F> {
		inner: F,
		encoded: Option<Vec<u8>>,
	}

	impl<F: Fn() -> Vec<u8>> traits::Lazy<[u8]> for LazyEncode<F> {
		fn get(&mut self) -> &[u8] {
			self.encoded.get_or_insert_with(&self.inner).as_slice()
		}
	}

	sig.verify(
		LazyEncode { inner: || item.encode(), encoded: None },
		signer,
	)
}

/// Helper macro for `impl_outer_config`
#[macro_export]
macro_rules! __impl_outer_config_types {
	// Generic + Instance
	(
		$concrete:ident $config:ident $snake:ident { $instance:ident } < $ignore:ident >;
		$( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig<$concrete, $snake::$instance>;
		$crate::__impl_outer_config_types! { $concrete $( $rest )* }
	};
	// Generic
	(
		$concrete:ident $config:ident $snake:ident < $ignore:ident >;
		$( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig<$concrete>;
		$crate::__impl_outer_config_types! { $concrete $( $rest )* }
	};
	// No Generic and maybe Instance
	(
		$concrete:ident $config:ident $snake:ident $( { $instance:ident } )?;
		$( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig;
		$crate::__impl_outer_config_types! { $concrete $( $rest )* }
	};
	($concrete:ident) => ()
}

/// Implement the output "meta" module configuration struct,
/// which is basically:
/// pub struct GenesisConfig {
/// 	rust_module_one: Option<ModuleOneConfig>,
/// 	...
/// }
#[macro_export]
macro_rules! impl_outer_config {
	(
		pub struct $main:ident for $concrete:ident {
			$( $config:ident =>
				$snake:ident $( $instance:ident )? $( <$generic:ident> )*, )*
		}
	) => {
		$crate::__impl_outer_config_types! {
			$concrete $( $config $snake $( { $instance } )? $( <$generic> )*; )*
		}

		$crate::paste::item! {
			#[cfg(any(feature = "std", test))]
			#[derive($crate::serde::Serialize, $crate::serde::Deserialize)]
			#[serde(rename_all = "camelCase")]
			#[serde(deny_unknown_fields)]
			pub struct $main {
				$(
					pub [< $snake $(_ $instance )? >]: Option<$config>,
				)*
			}
			#[cfg(any(feature = "std", test))]
			impl $crate::BuildStorage for $main {
				fn assimilate_storage(
					&self,
					storage: &mut $crate::Storage,
				) -> std::result::Result<(), String> {
					$(
						if let Some(ref extra) = self.[< $snake $(_ $instance )? >] {
							$crate::impl_outer_config! {
								@CALL_FN
								$concrete;
								$snake;
								$( $instance )?;
								extra;
								storage;
							}
						}
					)*
					Ok(())
				}
			}
		}
	};
	(@CALL_FN
		$runtime:ident;
		$module:ident;
		$instance:ident;
		$extra:ident;
		$storage:ident;
	) => {
		$crate::BuildModuleGenesisStorage::<$runtime, $module::$instance>::build_module_genesis_storage(
			$extra,
			$storage,
		)?;
	};
	(@CALL_FN
		$runtime:ident;
		$module:ident;
		;
		$extra:ident;
		$storage:ident;
	) => {
		$crate::BuildModuleGenesisStorage::<$runtime, $module::__InherentHiddenInstance>::build_module_genesis_storage(
			$extra,
			$storage,
		)?;
	}
}

/// Checks that `$x` is equal to `$y` with an error rate of `$error`.
///
/// # Example
///
/// ```rust
/// # fn main() {
/// sp_runtime::assert_eq_error_rate!(10, 10, 0);
/// sp_runtime::assert_eq_error_rate!(10, 11, 1);
/// sp_runtime::assert_eq_error_rate!(12, 10, 2);
/// # }
/// ```
///
/// ```rust,should_panic
/// # fn main() {
/// sp_runtime::assert_eq_error_rate!(12, 10, 1);
/// # }
/// ```
#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_eq_error_rate {
	($x:expr, $y:expr, $error:expr $(,)?) => {
		assert!(
			($x) >= (($y) - ($error)) && ($x) <= (($y) + ($error)),
			"{:?} != {:?} (with error rate {:?})",
			$x,
			$y,
			$error,
		);
	};
}

/// Simple blob to hold an extrinsic without committing to its format and ensure it is serialized
/// correctly.
#[derive(PartialEq, Eq, Clone, Default, Encode, Decode)]
pub struct OpaqueExtrinsic(pub Vec<u8>);

#[cfg(feature = "std")]
impl parity_util_mem::MallocSizeOf for OpaqueExtrinsic {
	fn size_of(&self, ops: &mut parity_util_mem::MallocSizeOfOps) -> usize {
		self.0.size_of(ops)
	}
}

impl sp_std::fmt::Debug for OpaqueExtrinsic {
	#[cfg(feature = "std")]
	fn fmt(&self, fmt: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(fmt, "{}", sp_core::hexdisplay::HexDisplay::from(&self.0))
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _fmt: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}


#[cfg(feature = "std")]
impl ::serde::Serialize for OpaqueExtrinsic {
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		codec::Encode::using_encoded(&self.0, |bytes| ::sp_core::bytes::serialize(bytes, seq))
	}
}

#[cfg(feature = "std")]
impl<'a> ::serde::Deserialize<'a> for OpaqueExtrinsic {
	fn deserialize<D>(de: D) -> Result<Self, D::Error> where D: ::serde::Deserializer<'a> {
		let r = ::sp_core::bytes::deserialize(de)?;
		Decode::decode(&mut &r[..])
			.map_err(|e| ::serde::de::Error::custom(format!("Decode error: {}", e)))
	}
}

impl traits::Extrinsic for OpaqueExtrinsic {
	type Call = ();
	type SignaturePayload = ();
}

/// Print something that implements `Printable` from the runtime.
pub fn print(print: impl traits::Printable) {
	print.print();
}


/// Batching session.
///
/// To be used in runtime only. Outside of runtime, just construct
/// `BatchVerifier` directly.
#[must_use = "`verify()` needs to be called to finish batch signature verification!"]
pub struct SignatureBatching(bool);

impl SignatureBatching {
	/// Start new batching session.
	pub fn start() -> Self {
		sp_io::crypto::start_batch_verify();
		SignatureBatching(false)
	}

	/// Verify all signatures submitted during the batching session.
	#[must_use]
	pub fn verify(mut self) -> bool {
		self.0 = true;
		sp_io::crypto::finish_batch_verify()
	}
}

impl Drop for SignatureBatching {
	fn drop(&mut self) {
		// Sanity check. If user forgets to actually call `verify()`.
		if !self.0 {
			panic!("Signature verification has not been called before `SignatureBatching::drop`")
		}
	}
}


#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Encode, Decode};
	use sp_core::crypto::Pair;

	#[test]
	fn opaque_extrinsic_serialization() {
		let ex = super::OpaqueExtrinsic(vec![1, 2, 3, 4]);
		assert_eq!(serde_json::to_string(&ex).unwrap(), "\"0x1001020304\"".to_owned());
	}

	#[test]
	fn dispatch_error_encoding() {
		let error = DispatchError::Module {
			index: 1,
			error: 2,
			message: Some("error message"),
		};
		let encoded = error.encode();
		let decoded = DispatchError::decode(&mut &encoded[..]).unwrap();
		assert_eq!(encoded, vec![3, 1, 2]);
		assert_eq!(
			decoded,
			DispatchError::Module {
				index: 1,
				error: 2,
				message: None,
			},
		);
	}

	#[test]
	fn multi_signature_ecdsa_verify_works() {
		let msg = &b"test-message"[..];
		let (pair, _) = ecdsa::Pair::generate();

		let signature = pair.sign(&msg);
		assert!(ecdsa::Pair::verify(&signature, msg, &pair.public()));

		let multi_sig = MultiSignature::from(signature);
		let multi_signer = MultiSigner::from(pair.public());
		assert!(multi_sig.verify(msg, &multi_signer.into_account()));

		let multi_signer = MultiSigner::from(pair.public());
		assert!(multi_sig.verify(msg, &multi_signer.into_account()));
	}


	#[test]
	#[should_panic(expected = "Signature verification has not been called")]
	fn batching_still_finishes_when_not_called_directly() {
		let mut ext = sp_state_machine::BasicExternalities::with_tasks_executor();
		ext.execute_with(|| {
			let _batching = SignatureBatching::start();
			sp_io::crypto::sr25519_verify(
				&Default::default(),
				&Vec::new(),
				&Default::default(),
			);
		});
	}
}
