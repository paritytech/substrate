// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

#[doc(hidden)]
pub use codec;
#[cfg(feature = "std")]
#[doc(hidden)]
pub use serde;
#[doc(hidden)]
pub use rstd;

#[doc(hidden)]
pub use paste;

#[doc(hidden)]
pub use app_crypto;

#[cfg(feature = "std")]
pub use runtime_io::{StorageOverlay, ChildrenStorageOverlay};

use rstd::prelude::*;
use rstd::convert::TryFrom;
use primitives::{crypto, ed25519, sr25519, hash::{H256, H512}};
use codec::{Encode, Decode};

#[cfg(feature = "std")]
pub mod testing;

pub mod curve;
pub mod generic;
pub mod offchain;
pub mod sr_arithmetic;
pub mod traits;
pub mod transaction_validity;
pub mod weights;

/// Re-export these since they're only "kind of" generic.
pub use generic::{DigestItem, Digest};

/// Re-export this since it's part of the API of this crate.
pub use primitives::{TypeId, crypto::{key_types, KeyTypeId, CryptoType}};
pub use app_crypto::RuntimeAppPublic;

/// Re-export arithmetic stuff.
pub use sr_arithmetic::{
	Perquintill, Perbill, Permill, Percent,
	Rational128, Fixed64
};
/// Re-export 128 bit helpers from sr_arithmetic
pub use sr_arithmetic::helpers_128bit;

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

/// A String that is a `&'static str` on `no_std` and a `Cow<'static, str>` on `std`.
#[cfg(feature = "std")]
pub type RuntimeString = ::std::borrow::Cow<'static, str>;
/// A String that is a `&'static str` on `no_std` and a `Cow<'static, str>` on `std`.
#[cfg(not(feature = "std"))]
pub type RuntimeString = &'static str;

/// Create a const [RuntimeString].
#[cfg(feature = "std")]
#[macro_export]
macro_rules! create_runtime_str {
	( $y:expr ) => {{ ::std::borrow::Cow::Borrowed($y) }}
}

/// Create a const [RuntimeString].
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! create_runtime_str {
	( $y:expr ) => {{ $y }}
}

#[cfg(feature = "std")]
pub use serde::{Serialize, Deserialize, de::DeserializeOwned};

/// Complex storage builder stuff.
#[cfg(feature = "std")]
pub trait BuildStorage: Sized {
	/// Build the storage out of this builder.
	fn build_storage(self) -> Result<(StorageOverlay, ChildrenStorageOverlay), String> {
		let mut storage = (Default::default(), Default::default());
		self.assimilate_storage(&mut storage)?;
		Ok(storage)
	}
	/// Assimilate the storage for this module into pre-existing overlays.
	fn assimilate_storage(
		self,
		storage: &mut (StorageOverlay, ChildrenStorageOverlay),
	) -> Result<(), String>;
}

/// Something that can build the genesis storage of a module.
#[cfg(feature = "std")]
pub trait BuildModuleGenesisStorage<T, I>: Sized {
	/// Create the module genesis storage into the given `storage` and `child_storage`.
	fn build_module_genesis_storage(
		self,
		storage: &mut (StorageOverlay, ChildrenStorageOverlay),
	) -> Result<(), String>;
}

#[cfg(feature = "std")]
impl BuildStorage for (StorageOverlay, ChildrenStorageOverlay) {
	fn build_storage(self) -> Result<(StorageOverlay, ChildrenStorageOverlay), String> {
		Ok(self)
	}
	fn assimilate_storage(
		self,
		storage: &mut (StorageOverlay, ChildrenStorageOverlay),
	)-> Result<(), String> {
		storage.0.extend(self.0);
		for (k, other_map) in self.1.into_iter() {
			if let Some(map) = storage.1.get_mut(&k) {
				map.extend(other_map);
			} else {
				storage.1.insert(k, other_map);
			}
		}
		Ok(())
	}
}

/// Consensus engine unique ID.
pub type ConsensusEngineId = [u8; 4];

/// Signature verify that can work with any known signature types..
#[derive(Eq, PartialEq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum MultiSignature {
	/// An Ed25519 signature.
	Ed25519(ed25519::Signature),
	/// An Sr25519 signature.
	Sr25519(sr25519::Signature),
}

impl From<ed25519::Signature> for MultiSignature {
	fn from(x: ed25519::Signature) -> Self {
		MultiSignature::Ed25519(x)
	}
}

impl From<sr25519::Signature> for MultiSignature {
	fn from(x: sr25519::Signature) -> Self {
		MultiSignature::Sr25519(x)
	}
}

impl Default for MultiSignature {
	fn default() -> Self {
		MultiSignature::Ed25519(Default::default())
	}
}

/// Public key for any known crypto algorithm.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub enum MultiSigner {
	/// An Ed25519 identity.
	Ed25519(ed25519::Public),
	/// An Sr25519 identity.
	Sr25519(sr25519::Public),
}

impl Default for MultiSigner {
	fn default() -> Self {
		MultiSigner::Ed25519(Default::default())
	}
}

/// NOTE: This implementations is required by `SimpleAddressDeterminator`,
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
		}
	}
}

impl From<ed25519::Public> for MultiSigner {
	fn from(x: ed25519::Public) -> Self {
		MultiSigner::Ed25519(x)
	}
}

impl From<sr25519::Public> for MultiSigner {
	fn from(x: sr25519::Public) -> Self {
		MultiSigner::Sr25519(x)
	}
}

 #[cfg(feature = "std")]
impl std::fmt::Display for MultiSigner {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			MultiSigner::Ed25519(ref who) => write!(fmt, "ed25519: {}", who),
			MultiSigner::Sr25519(ref who) => write!(fmt, "sr25519: {}", who),
		}
	}
}

impl Verify for MultiSignature {
	type Signer = MultiSigner;
	fn verify<L: Lazy<[u8]>>(&self, msg: L, signer: &Self::Signer) -> bool {
		match (self, signer) {
			(MultiSignature::Ed25519(ref sig), &MultiSigner::Ed25519(ref who)) => sig.verify(msg, who),
			(MultiSignature::Sr25519(ref sig), &MultiSigner::Sr25519(ref who)) => sig.verify(msg, who),
			_ => false,
		}
	}
}

/// Signature verify that can work with any known signature types..
#[derive(Eq, PartialEq, Clone, Default, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub struct AnySignature(H512);

impl Verify for AnySignature {
	type Signer = sr25519::Public;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &sr25519::Public) -> bool {
		sr25519::Signature::try_from(self.0.as_fixed_bytes().as_ref())
			.map(|s| runtime_io::sr25519_verify(&s, msg.get(), &signer))
			.unwrap_or(false)
		|| ed25519::Signature::try_from(self.0.as_fixed_bytes().as_ref())
			.and_then(|s| ed25519::Public::try_from(signer.0.as_ref()).map(|p| (s, p)))
			.map(|(s, p)| runtime_io::ed25519_verify(&s, msg.get(), &p))
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

#[derive(Eq, PartialEq, Clone, Copy, Decode, Encode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
/// Reason why an extrinsic couldn't be applied (i.e. invalid extrinsic).
pub enum ApplyError {
	/// General error to do with the permissions of the sender.
	NoPermission,

	/// General error to do with the state of the system in general.
	BadState,

	/// Any error to do with the transaction validity.
	Validity(transaction_validity::TransactionValidityError),
}

impl ApplyError {
	/// Returns if the reason for the error was block resource exhaustion.
	pub fn exhausted_resources(&self) -> bool {
		match self {
			Self::Validity(e) => e.exhausted_resources(),
			_ => false,
		}
	}
}

impl From<ApplyError> for &'static str {
	fn from(err: ApplyError) -> &'static str {
		match err {
			ApplyError::NoPermission => "Transaction does not have required permissions",
			ApplyError::BadState => "System state currently prevents this transaction",
			ApplyError::Validity(v) => v.into(),
		}
	}
}

impl From<transaction_validity::TransactionValidityError> for ApplyError {
	fn from(err: transaction_validity::TransactionValidityError) -> Self {
		ApplyError::Validity(err)
	}
}

/// The outcome of applying a transaction.
pub type ApplyOutcome = Result<(), DispatchError>;

impl From<DispatchError> for ApplyOutcome {
	fn from(err: DispatchError) -> Self {
		Err(err)
	}
}

/// Result from attempt to apply an extrinsic.
pub type ApplyResult = Result<ApplyOutcome, ApplyError>;

#[derive(Eq, PartialEq, Clone, Copy, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
/// Reason why a dispatch call failed
pub struct DispatchError {
	/// Module index, matching the metadata module index
	pub module: Option<u8>,
	/// Module specific error value
	pub error: u8,
	/// Optional error message.
	#[codec(skip)]
	pub message: Option<&'static str>,
}

impl DispatchError {
	/// Create a new instance of `DispatchError`.
	pub fn new(module: Option<u8>, error: u8, message: Option<&'static str>) -> Self {
		Self {
			module,
			error,
			message,
		}
	}
}

impl traits::Printable for DispatchError {
	fn print(&self) {
		"DispatchError".print();
		if let Some(module) = self.module {
			module.print();
		}
		self.error.print();
		if let Some(msg) = self.message {
			msg.print();
		}
	}
}

impl traits::ModuleDispatchError for &'static str {
	fn as_u8(&self) -> u8 {
		0
	}

	fn as_str(&self) -> &'static str {
		self
	}
}

impl From<&'static str> for DispatchError {
	fn from(err: &'static str) -> DispatchError {
		DispatchError::new(None, 0, Some(err))
	}
}

/// Verify a signature on an encoded value in a lazy manner. This can be
/// an optimization if the signature scheme has an "unsigned" escape hash.
pub fn verify_encoded_lazy<V: Verify, T: codec::Encode>(sig: &V, item: &T, signer: &V::Signer) -> bool {
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
					self,
					storage: &mut ($crate::StorageOverlay, $crate::ChildrenStorageOverlay),
				) -> std::result::Result<(), String> {
					$(
						if let Some(extra) = self.[< $snake $(_ $instance )? >] {
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
/// sr_primitives::assert_eq_error_rate!(10, 10, 0);
/// sr_primitives::assert_eq_error_rate!(10, 11, 1);
/// sr_primitives::assert_eq_error_rate!(12, 10, 2);
/// # }
/// ```
///
/// ```rust,should_panic
/// # fn main() {
/// sr_primitives::assert_eq_error_rate!(12, 10, 1);
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
impl std::fmt::Debug for OpaqueExtrinsic {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(fmt, "{}", primitives::hexdisplay::HexDisplay::from(&self.0))
	}
}

#[cfg(feature = "std")]
impl ::serde::Serialize for OpaqueExtrinsic {
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		codec::Encode::using_encoded(&self.0, |bytes| ::primitives::bytes::serialize(bytes, seq))
	}
}

#[cfg(feature = "std")]
impl<'a> ::serde::Deserialize<'a> for OpaqueExtrinsic {
	fn deserialize<D>(de: D) -> Result<Self, D::Error> where D: ::serde::Deserializer<'a> {
		let r = ::primitives::bytes::deserialize(de)?;
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

#[cfg(test)]
mod tests {
	use crate::DispatchError;
	use codec::{Encode, Decode};

	#[test]
	fn opaque_extrinsic_serialization() {
		let ex = super::OpaqueExtrinsic(vec![1, 2, 3, 4]);
		assert_eq!(serde_json::to_string(&ex).unwrap(), "\"0x1001020304\"".to_owned());
	}

	#[test]
	fn dispatch_error_encoding() {
		let error = DispatchError {
			module: Some(1),
			error: 2,
			message: Some("error message"),
		};
		let encoded = error.encode();
		let decoded = DispatchError::decode(&mut &encoded[..]).unwrap();
		assert_eq!(encoded, vec![1, 1, 2]);
		assert_eq!(
			decoded,
			DispatchError {
				module: Some(1),
				error: 2,
				message: None,
			},
		);
	}
}
