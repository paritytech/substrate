// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Runtime Modules shared primitive types.

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

#[doc(hidden)]
pub use codec;
#[doc(hidden)]
pub use scale_info;
#[cfg(feature = "std")]
#[doc(hidden)]
pub use serde;
#[doc(hidden)]
pub use sp_std;

#[doc(hidden)]
pub use paste;
#[doc(hidden)]
pub use sp_arithmetic::traits::Saturating;

#[doc(hidden)]
pub use sp_application_crypto as app_crypto;

pub use sp_core::storage::StateVersion;
#[cfg(feature = "std")]
pub use sp_core::storage::{Storage, StorageChild};

use sp_core::{
	crypto::{self, ByteArray},
	ecdsa, ed25519,
	hash::{H256, H512},
	sr25519,
};
use sp_std::prelude::*;

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

pub mod curve;
pub mod generic;
pub mod legacy;
mod multiaddress;
pub mod offchain;
pub mod runtime_logger;
mod runtime_string;
#[cfg(feature = "std")]
pub mod testing;
pub mod traits;
pub mod transaction_validity;

pub use crate::runtime_string::*;

// Re-export Multiaddress
pub use multiaddress::MultiAddress;

/// Re-export these since they're only "kind of" generic.
pub use generic::{Digest, DigestItem};

pub use sp_application_crypto::{BoundToRuntimeAppPublic, RuntimeAppPublic};
/// Re-export this since it's part of the API of this crate.
pub use sp_core::{
	bounded::{BoundedBTreeMap, BoundedBTreeSet, BoundedSlice, BoundedVec, WeakBoundedVec},
	crypto::{key_types, AccountId32, CryptoType, CryptoTypeId, KeyTypeId},
	TypeId,
};
/// Re-export bounded_vec and bounded_btree_map macros only when std is enabled.
#[cfg(feature = "std")]
pub use sp_core::{bounded_btree_map, bounded_vec};

/// Re-export `RuntimeDebug`, to avoid dependency clutter.
pub use sp_core::RuntimeDebug;

/// Re-export big_uint stuff.
pub use sp_arithmetic::biguint;
/// Re-export 128 bit helpers.
pub use sp_arithmetic::helpers_128bit;
/// Re-export top-level arithmetic stuff.
pub use sp_arithmetic::{
	traits::SaturatedConversion, ArithmeticError, FixedI128, FixedI64, FixedPointNumber,
	FixedPointOperand, FixedU128, InnerOf, PerThing, PerU16, Perbill, Percent, Permill,
	Perquintill, Rational128, Rounding, UpperOf,
};

pub use either::Either;

/// The number of bytes of the module-specific `error` field defined in [`ModuleError`].
/// In FRAME, this is the maximum encoded size of a pallet error type.
pub const MAX_MODULE_ERROR_ENCODED_SIZE: usize = 4;

/// An abstraction over justification for a block's validity under a consensus algorithm.
///
/// Essentially a finality proof. The exact formulation will vary between consensus
/// algorithms. In the case where there are multiple valid proofs, inclusion within
/// the block itself would allow swapping justifications to change the block's hash
/// (and thus fork the chain). Sending a `Justification` alongside a block instead
/// bypasses this problem.
///
/// Each justification is provided as an encoded blob, and is tagged with an ID
/// to identify the consensus engine that generated the proof (we might have
/// multiple justifications from different engines for the same block).
pub type Justification = (ConsensusEngineId, EncodedJustification);

/// The encoded justification specific to a consensus engine.
pub type EncodedJustification = Vec<u8>;

/// Collection of justifications for a given block, multiple justifications may
/// be provided by different consensus engines for the same block.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode)]
pub struct Justifications(Vec<Justification>);

impl Justifications {
	/// Return an iterator over the justifications.
	pub fn iter(&self) -> impl Iterator<Item = &Justification> {
		self.0.iter()
	}

	/// Append a justification. Returns false if a justification with the same
	/// `ConsensusEngineId` already exists, in which case the justification is
	/// not inserted.
	pub fn append(&mut self, justification: Justification) -> bool {
		if self.get(justification.0).is_some() {
			return false
		}
		self.0.push(justification);
		true
	}

	/// Return the encoded justification for the given consensus engine, if it
	/// exists.
	pub fn get(&self, engine_id: ConsensusEngineId) -> Option<&EncodedJustification> {
		self.iter().find(|j| j.0 == engine_id).map(|j| &j.1)
	}

	/// Remove the encoded justification for the given consensus engine, if it exists.
	pub fn remove(&mut self, engine_id: ConsensusEngineId) {
		self.0.retain(|j| j.0 != engine_id)
	}

	/// Return a copy of the encoded justification for the given consensus
	/// engine, if it exists.
	pub fn into_justification(self, engine_id: ConsensusEngineId) -> Option<EncodedJustification> {
		self.into_iter().find(|j| j.0 == engine_id).map(|j| j.1)
	}
}

impl IntoIterator for Justifications {
	type Item = Justification;
	type IntoIter = sp_std::vec::IntoIter<Self::Item>;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl From<Justification> for Justifications {
	fn from(justification: Justification) -> Self {
		Self(vec![justification])
	}
}

use traits::{Lazy, Verify};

use crate::traits::IdentifyAccount;
#[cfg(feature = "std")]
pub use serde::{de::DeserializeOwned, Deserialize, Serialize};

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
	fn assimilate_storage(&self, storage: &mut sp_core::storage::Storage) -> Result<(), String>;
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
	fn assimilate_storage(&self, storage: &mut sp_core::storage::Storage) -> Result<(), String> {
		storage.top.extend(self.top.iter().map(|(k, v)| (k.clone(), v.clone())));
		for (k, other_map) in self.children_default.iter() {
			let k = k.clone();
			if let Some(map) = storage.children_default.get_mut(&k) {
				map.data.extend(other_map.data.iter().map(|(k, v)| (k.clone(), v.clone())));
				if !map.child_info.try_update(&other_map.child_info) {
					return Err("Incompatible child info update".to_string())
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
	fn assimilate_storage(&self, _: &mut sp_core::storage::Storage) -> Result<(), String> {
		Err("`assimilate_storage` not implemented for `()`".into())
	}
}

/// Consensus engine unique ID.
pub type ConsensusEngineId = [u8; 4];

/// Signature verify that can work with any known signature types.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Eq, PartialEq, Clone, Encode, Decode, MaxEncodedLen, RuntimeDebug, TypeInfo)]
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
		Self::Ed25519(x)
	}
}

impl TryFrom<MultiSignature> for ed25519::Signature {
	type Error = ();
	fn try_from(m: MultiSignature) -> Result<Self, Self::Error> {
		if let MultiSignature::Ed25519(x) = m {
			Ok(x)
		} else {
			Err(())
		}
	}
}

impl From<sr25519::Signature> for MultiSignature {
	fn from(x: sr25519::Signature) -> Self {
		Self::Sr25519(x)
	}
}

impl TryFrom<MultiSignature> for sr25519::Signature {
	type Error = ();
	fn try_from(m: MultiSignature) -> Result<Self, Self::Error> {
		if let MultiSignature::Sr25519(x) = m {
			Ok(x)
		} else {
			Err(())
		}
	}
}

impl From<ecdsa::Signature> for MultiSignature {
	fn from(x: ecdsa::Signature) -> Self {
		Self::Ecdsa(x)
	}
}

impl TryFrom<MultiSignature> for ecdsa::Signature {
	type Error = ();
	fn try_from(m: MultiSignature) -> Result<Self, Self::Error> {
		if let MultiSignature::Ecdsa(x) = m {
			Ok(x)
		} else {
			Err(())
		}
	}
}

/// Public key for any known crypto algorithm.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum MultiSigner {
	/// An Ed25519 identity.
	Ed25519(ed25519::Public),
	/// An Sr25519 identity.
	Sr25519(sr25519::Public),
	/// An SECP256k1/ECDSA identity (actually, the Blake2 hash of the compressed pub key).
	Ecdsa(ecdsa::Public),
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
			Self::Ed25519(ref who) => who.as_ref(),
			Self::Sr25519(ref who) => who.as_ref(),
			Self::Ecdsa(ref who) => who.as_ref(),
		}
	}
}

impl traits::IdentifyAccount for MultiSigner {
	type AccountId = AccountId32;
	fn into_account(self) -> AccountId32 {
		match self {
			Self::Ed25519(who) => <[u8; 32]>::from(who).into(),
			Self::Sr25519(who) => <[u8; 32]>::from(who).into(),
			Self::Ecdsa(who) => sp_io::hashing::blake2_256(who.as_ref()).into(),
		}
	}
}

impl From<ed25519::Public> for MultiSigner {
	fn from(x: ed25519::Public) -> Self {
		Self::Ed25519(x)
	}
}

impl TryFrom<MultiSigner> for ed25519::Public {
	type Error = ();
	fn try_from(m: MultiSigner) -> Result<Self, Self::Error> {
		if let MultiSigner::Ed25519(x) = m {
			Ok(x)
		} else {
			Err(())
		}
	}
}

impl From<sr25519::Public> for MultiSigner {
	fn from(x: sr25519::Public) -> Self {
		Self::Sr25519(x)
	}
}

impl TryFrom<MultiSigner> for sr25519::Public {
	type Error = ();
	fn try_from(m: MultiSigner) -> Result<Self, Self::Error> {
		if let MultiSigner::Sr25519(x) = m {
			Ok(x)
		} else {
			Err(())
		}
	}
}

impl From<ecdsa::Public> for MultiSigner {
	fn from(x: ecdsa::Public) -> Self {
		Self::Ecdsa(x)
	}
}

impl TryFrom<MultiSigner> for ecdsa::Public {
	type Error = ();
	fn try_from(m: MultiSigner) -> Result<Self, Self::Error> {
		if let MultiSigner::Ecdsa(x) = m {
			Ok(x)
		} else {
			Err(())
		}
	}
}

#[cfg(feature = "std")]
impl std::fmt::Display for MultiSigner {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			Self::Ed25519(ref who) => write!(fmt, "ed25519: {}", who),
			Self::Sr25519(ref who) => write!(fmt, "sr25519: {}", who),
			Self::Ecdsa(ref who) => write!(fmt, "ecdsa: {}", who),
		}
	}
}

impl Verify for MultiSignature {
	type Signer = MultiSigner;
	fn verify<L: Lazy<[u8]>>(&self, mut msg: L, signer: &AccountId32) -> bool {
		match (self, signer) {
			(Self::Ed25519(ref sig), who) => match ed25519::Public::from_slice(who.as_ref()) {
				Ok(signer) => sig.verify(msg, &signer),
				Err(()) => false,
			},
			(Self::Sr25519(ref sig), who) => match sr25519::Public::from_slice(who.as_ref()) {
				Ok(signer) => sig.verify(msg, &signer),
				Err(()) => false,
			},
			(Self::Ecdsa(ref sig), who) => {
				let m = sp_io::hashing::blake2_256(msg.get());
				match sp_io::crypto::secp256k1_ecdsa_recover_compressed(sig.as_ref(), &m) {
					Ok(pubkey) =>
						&sp_io::hashing::blake2_256(pubkey.as_ref()) ==
							<dyn AsRef<[u8; 32]>>::as_ref(who),
					_ => false,
				}
			},
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
			.unwrap_or(false) ||
			ed25519::Signature::try_from(self.0.as_fixed_bytes().as_ref())
				.map(|s| match ed25519::Public::from_slice(signer.as_ref()) {
					Err(()) => false,
					Ok(signer) => s.verify(msg, &signer),
				})
				.unwrap_or(false)
	}
}

impl From<sr25519::Signature> for AnySignature {
	fn from(s: sr25519::Signature) -> Self {
		Self(s.into())
	}
}

impl From<ed25519::Signature> for AnySignature {
	fn from(s: ed25519::Signature) -> Self {
		Self(s.into())
	}
}

impl From<DispatchError> for DispatchOutcome {
	fn from(err: DispatchError) -> Self {
		Err(err)
	}
}

/// This is the legacy return type of `Dispatchable`. It is still exposed for compatibility reasons.
/// The new return type is `DispatchResultWithInfo`. FRAME runtimes should use
/// `frame_support::dispatch::DispatchResult`.
pub type DispatchResult = sp_std::result::Result<(), DispatchError>;

/// Return type of a `Dispatchable` which contains the `DispatchResult` and additional information
/// about the `Dispatchable` that is only known post dispatch.
pub type DispatchResultWithInfo<T> = sp_std::result::Result<T, DispatchErrorWithPostInfo<T>>;

/// Reason why a pallet call failed.
#[derive(Eq, Clone, Copy, Encode, Decode, Debug, TypeInfo, MaxEncodedLen)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct ModuleError {
	/// Module index, matching the metadata module index.
	pub index: u8,
	/// Module specific error value.
	pub error: [u8; MAX_MODULE_ERROR_ENCODED_SIZE],
	/// Optional error message.
	#[codec(skip)]
	#[cfg_attr(feature = "std", serde(skip_deserializing))]
	pub message: Option<&'static str>,
}

impl PartialEq for ModuleError {
	fn eq(&self, other: &Self) -> bool {
		(self.index == other.index) && (self.error == other.error)
	}
}

/// Errors related to transactional storage layers.
#[derive(Eq, PartialEq, Clone, Copy, Encode, Decode, Debug, TypeInfo, MaxEncodedLen)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum TransactionalError {
	/// Too many transactional layers have been spawned.
	LimitReached,
	/// A transactional layer was expected, but does not exist.
	NoLayer,
}

impl From<TransactionalError> for &'static str {
	fn from(e: TransactionalError) -> &'static str {
		match e {
			TransactionalError::LimitReached => "Too many transactional layers have been spawned",
			TransactionalError::NoLayer => "A transactional layer was expected, but does not exist",
		}
	}
}

impl From<TransactionalError> for DispatchError {
	fn from(e: TransactionalError) -> DispatchError {
		Self::Transactional(e)
	}
}

/// Reason why a dispatch call failed.
#[derive(Eq, Clone, Copy, Encode, Decode, Debug, TypeInfo, PartialEq, MaxEncodedLen)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum DispatchError {
	/// Some error occurred.
	Other(
		#[codec(skip)]
		#[cfg_attr(feature = "std", serde(skip_deserializing))]
		&'static str,
	),
	/// Failed to lookup some data.
	CannotLookup,
	/// A bad origin.
	BadOrigin,
	/// A custom error in a module.
	Module(ModuleError),
	/// At least one consumer is remaining so the account cannot be destroyed.
	ConsumerRemaining,
	/// There are no providers so the account cannot be created.
	NoProviders,
	/// There are too many consumers so the account cannot be created.
	TooManyConsumers,
	/// An error to do with tokens.
	Token(TokenError),
	/// An arithmetic error.
	Arithmetic(ArithmeticError),
	/// The number of transactional layers has been reached, or we are not in a transactional
	/// layer.
	Transactional(TransactionalError),
	/// Resources exhausted, e.g. attempt to read/write data which is too large to manipulate.
	Exhausted,
	/// The state is corrupt; this is generally not going to fix itself.
	Corruption,
	/// Some resource (e.g. a preimage) is unavailable right now. This might fix itself later.
	Unavailable,
	/// Root origin is not allowed.
	RootNotAllowed,
}

/// Result of a `Dispatchable` which contains the `DispatchResult` and additional information about
/// the `Dispatchable` that is only known post dispatch.
#[derive(Eq, PartialEq, Clone, Copy, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct DispatchErrorWithPostInfo<Info>
where
	Info: Eq + PartialEq + Clone + Copy + Encode + Decode + traits::Printable,
{
	/// Additional information about the `Dispatchable` which is only known post dispatch.
	pub post_info: Info,
	/// The actual `DispatchResult` indicating whether the dispatch was successful.
	pub error: DispatchError,
}

impl DispatchError {
	/// Return the same error but without the attached message.
	pub fn stripped(self) -> Self {
		match self {
			DispatchError::Module(ModuleError { index, error, message: Some(_) }) =>
				DispatchError::Module(ModuleError { index, error, message: None }),
			m => m,
		}
	}
}

impl<T, E> From<E> for DispatchErrorWithPostInfo<T>
where
	T: Eq + PartialEq + Clone + Copy + Encode + Decode + traits::Printable + Default,
	E: Into<DispatchError>,
{
	fn from(error: E) -> Self {
		Self { post_info: Default::default(), error: error.into() }
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

/// Description of what went wrong when trying to complete an operation on a token.
#[derive(Eq, PartialEq, Clone, Copy, Encode, Decode, Debug, TypeInfo, MaxEncodedLen)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum TokenError {
	/// Funds are unavailable.
	FundsUnavailable,
	/// Some part of the balance gives the only provider reference to the account and thus cannot
	/// be (re)moved.
	OnlyProvider,
	/// Account cannot exist with the funds that would be given.
	BelowMinimum,
	/// Account cannot be created.
	CannotCreate,
	/// The asset in question is unknown.
	UnknownAsset,
	/// Funds exist but are frozen.
	Frozen,
	/// Operation is not supported by the asset.
	Unsupported,
	/// Account cannot be created for a held balance.
	CannotCreateHold,
	/// Withdrawal would cause unwanted loss of account.
	NotExpendable,
}

impl From<TokenError> for &'static str {
	fn from(e: TokenError) -> &'static str {
		match e {
			TokenError::FundsUnavailable => "Funds are unavailable",
			TokenError::OnlyProvider => "Account that must exist would die",
			TokenError::BelowMinimum => "Account cannot exist with the funds that would be given",
			TokenError::CannotCreate => "Account cannot be created",
			TokenError::UnknownAsset => "The asset in question is unknown",
			TokenError::Frozen => "Funds exist but are frozen",
			TokenError::Unsupported => "Operation is not supported by the asset",
			TokenError::CannotCreateHold =>
				"Account cannot be created for recording amount on hold",
			TokenError::NotExpendable => "Account that is desired to remain would die",
		}
	}
}

impl From<TokenError> for DispatchError {
	fn from(e: TokenError) -> DispatchError {
		Self::Token(e)
	}
}

impl From<ArithmeticError> for DispatchError {
	fn from(e: ArithmeticError) -> DispatchError {
		Self::Arithmetic(e)
	}
}

impl From<&'static str> for DispatchError {
	fn from(err: &'static str) -> DispatchError {
		Self::Other(err)
	}
}

impl From<DispatchError> for &'static str {
	fn from(err: DispatchError) -> &'static str {
		use DispatchError::*;
		match err {
			Other(msg) => msg,
			CannotLookup => "Cannot lookup",
			BadOrigin => "Bad origin",
			Module(ModuleError { message, .. }) => message.unwrap_or("Unknown module error"),
			ConsumerRemaining => "Consumer remaining",
			NoProviders => "No providers",
			TooManyConsumers => "Too many consumers",
			Token(e) => e.into(),
			Arithmetic(e) => e.into(),
			Transactional(e) => e.into(),
			Exhausted => "Resources exhausted",
			Corruption => "State corrupt",
			Unavailable => "Resource unavailable",
			RootNotAllowed => "Root not allowed",
		}
	}
}

impl<T> From<DispatchErrorWithPostInfo<T>> for &'static str
where
	T: Eq + PartialEq + Clone + Copy + Encode + Decode + traits::Printable,
{
	fn from(err: DispatchErrorWithPostInfo<T>) -> &'static str {
		err.error.into()
	}
}

impl traits::Printable for DispatchError {
	fn print(&self) {
		use DispatchError::*;
		"DispatchError".print();
		match self {
			Other(err) => err.print(),
			CannotLookup => "Cannot lookup".print(),
			BadOrigin => "Bad origin".print(),
			Module(ModuleError { index, error, message }) => {
				index.print();
				error.print();
				if let Some(msg) = message {
					msg.print();
				}
			},
			ConsumerRemaining => "Consumer remaining".print(),
			NoProviders => "No providers".print(),
			TooManyConsumers => "Too many consumers".print(),
			Token(e) => {
				"Token error: ".print();
				<&'static str>::from(*e).print();
			},
			Arithmetic(e) => {
				"Arithmetic error: ".print();
				<&'static str>::from(*e).print();
			},
			Transactional(e) => {
				"Transactional error: ".print();
				<&'static str>::from(*e).print();
			},
			Exhausted => "Resources exhausted".print(),
			Corruption => "State corrupt".print(),
			Unavailable => "Resource unavailable".print(),
			RootNotAllowed => "Root not allowed".print(),
		}
	}
}

impl<T> traits::Printable for DispatchErrorWithPostInfo<T>
where
	T: Eq + PartialEq + Clone + Copy + Encode + Decode + traits::Printable,
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
///   This doesn't necessarily mean that the extrinsic is invalid, since it can still be included in
///   the next block if it has enough spare weight available.
/// - The sender doesn't have enough funds to pay the transaction inclusion fee. Including such a
///   transaction in the block doesn't make sense.
/// - The extrinsic supplied a bad signature. This transaction won't become valid ever.
pub type ApplyExtrinsicResult =
	Result<DispatchOutcome, transaction_validity::TransactionValidityError>;

/// Same as `ApplyExtrinsicResult` but augmented with `PostDispatchInfo` on success.
pub type ApplyExtrinsicResultWithInfo<T> =
	Result<DispatchResultWithInfo<T>, transaction_validity::TransactionValidityError>;

/// Verify a signature on an encoded value in a lazy manner. This can be
/// an optimization if the signature scheme has an "unsigned" escape hash.
pub fn verify_encoded_lazy<V: Verify, T: codec::Encode>(
	sig: &V,
	item: &T,
	signer: &<V::Signer as IdentifyAccount>::AccountId,
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

	sig.verify(LazyEncode { inner: || item.encode(), encoded: None }, signer)
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
			($x >= $crate::Saturating::saturating_sub($y, $error)) &&
				($x <= $crate::Saturating::saturating_add($y, $error)),
			"{:?} != {:?} (with error rate {:?})",
			$x,
			$y,
			$error,
		);
	};
}

/// Same as [`assert_eq_error_rate`], but intended to be used with floating point number, or
/// generally those who do not have over/underflow potentials.
#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_eq_error_rate_float {
	($x:expr, $y:expr, $error:expr $(,)?) => {
		assert!(
			($x >= $y - $error) && ($x <= $y + $error),
			"{:?} != {:?} (with error rate {:?})",
			$x,
			$y,
			$error,
		);
	};
}

/// Simple blob to hold an extrinsic without committing to its format and ensure it is serialized
/// correctly.
#[derive(PartialEq, Eq, Clone, Default, Encode, Decode, TypeInfo)]
pub struct OpaqueExtrinsic(Vec<u8>);

impl OpaqueExtrinsic {
	/// Convert an encoded extrinsic to an `OpaqueExtrinsic`.
	pub fn from_bytes(mut bytes: &[u8]) -> Result<Self, codec::Error> {
		Self::decode(&mut bytes)
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
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error>
	where
		S: ::serde::Serializer,
	{
		codec::Encode::using_encoded(&self.0, |bytes| ::sp_core::bytes::serialize(bytes, seq))
	}
}

#[cfg(feature = "std")]
impl<'a> ::serde::Deserialize<'a> for OpaqueExtrinsic {
	fn deserialize<D>(de: D) -> Result<Self, D::Error>
	where
		D: ::serde::Deserializer<'a>,
	{
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

/// Describes on what should happen with a storage transaction.
pub enum TransactionOutcome<R> {
	/// Commit the transaction.
	Commit(R),
	/// Rollback the transaction.
	Rollback(R),
}

impl<R> TransactionOutcome<R> {
	/// Convert into the inner type.
	pub fn into_inner(self) -> R {
		match self {
			Self::Commit(r) => r,
			Self::Rollback(r) => r,
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::traits::BlakeTwo256;

	use super::*;
	use codec::{Decode, Encode};
	use sp_core::crypto::Pair;
	use sp_io::TestExternalities;
	use sp_state_machine::create_proof_check_backend;

	#[test]
	fn opaque_extrinsic_serialization() {
		let ex = super::OpaqueExtrinsic(vec![1, 2, 3, 4]);
		assert_eq!(serde_json::to_string(&ex).unwrap(), "\"0x1001020304\"".to_owned());
	}

	#[test]
	fn dispatch_error_encoding() {
		let error = DispatchError::Module(ModuleError {
			index: 1,
			error: [2, 0, 0, 0],
			message: Some("error message"),
		});
		let encoded = error.encode();
		let decoded = DispatchError::decode(&mut &encoded[..]).unwrap();
		assert_eq!(encoded, vec![3, 1, 2, 0, 0, 0]);
		assert_eq!(
			decoded,
			DispatchError::Module(ModuleError { index: 1, error: [2, 0, 0, 0], message: None })
		);
	}

	#[test]
	fn dispatch_error_equality() {
		use DispatchError::*;

		let variants = vec![
			Other("foo"),
			Other("bar"),
			CannotLookup,
			BadOrigin,
			Module(ModuleError { index: 1, error: [1, 0, 0, 0], message: None }),
			Module(ModuleError { index: 1, error: [2, 0, 0, 0], message: None }),
			Module(ModuleError { index: 2, error: [1, 0, 0, 0], message: None }),
			ConsumerRemaining,
			NoProviders,
			Token(TokenError::FundsUnavailable),
			Token(TokenError::OnlyProvider),
			Token(TokenError::BelowMinimum),
			Token(TokenError::CannotCreate),
			Token(TokenError::UnknownAsset),
			Token(TokenError::Frozen),
			Arithmetic(ArithmeticError::Overflow),
			Arithmetic(ArithmeticError::Underflow),
			Arithmetic(ArithmeticError::DivisionByZero),
		];
		for (i, variant) in variants.iter().enumerate() {
			for (j, other_variant) in variants.iter().enumerate() {
				if i == j {
					assert_eq!(variant, other_variant);
				} else {
					assert_ne!(variant, other_variant);
				}
			}
		}

		// Ignores `message` field in `Module` variant.
		assert_eq!(
			Module(ModuleError { index: 1, error: [1, 0, 0, 0], message: Some("foo") }),
			Module(ModuleError { index: 1, error: [1, 0, 0, 0], message: None }),
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
	fn execute_and_generate_proof_works() {
		use codec::Encode;
		use sp_state_machine::Backend;
		let mut ext = TestExternalities::default();

		ext.insert(b"a".to_vec(), vec![1u8; 33]);
		ext.insert(b"b".to_vec(), vec![2u8; 33]);
		ext.insert(b"c".to_vec(), vec![3u8; 33]);
		ext.insert(b"d".to_vec(), vec![4u8; 33]);

		let pre_root = *ext.backend.root();
		let (_, proof) = ext.execute_and_prove(|| {
			sp_io::storage::get(b"a");
			sp_io::storage::get(b"b");
			sp_io::storage::get(b"v");
			sp_io::storage::get(b"d");
		});

		let compact_proof = proof.clone().into_compact_proof::<BlakeTwo256>(pre_root).unwrap();
		let compressed_proof = zstd::stream::encode_all(&compact_proof.encode()[..], 0).unwrap();

		// just an example of how you'd inspect the size of the proof.
		println!("proof size: {:?}", proof.encoded_size());
		println!("compact proof size: {:?}", compact_proof.encoded_size());
		println!("zstd-compressed compact proof size: {:?}", &compressed_proof.len());

		// create a new trie-backed from the proof and make sure it contains everything
		let proof_check = create_proof_check_backend::<BlakeTwo256>(pre_root, proof).unwrap();
		assert_eq!(proof_check.storage(b"a",).unwrap().unwrap(), vec![1u8; 33]);

		let _ = ext.execute_and_prove(|| {
			sp_io::storage::set(b"a", &vec![1u8; 44]);
		});

		// ensure that these changes are propagated to the backend.

		ext.execute_with(|| {
			assert_eq!(sp_io::storage::get(b"a").unwrap(), vec![1u8; 44]);
			assert_eq!(sp_io::storage::get(b"b").unwrap(), vec![2u8; 33]);
		});
	}
}

// NOTE: we have to test the sp_core stuff also from a different crate to check that the macro
// can access the sp_core crate.
#[cfg(test)]
mod sp_core_tests {
	use super::*;

	#[test]
	#[should_panic]
	fn generate_feature_enabled_macro_panics() {
		sp_core::generate_feature_enabled_macro!(if_test, test, $);
		if_test!(panic!("This should panic"));
	}

	#[test]
	fn generate_feature_enabled_macro_works() {
		sp_core::generate_feature_enabled_macro!(if_not_test, not(test), $);
		if_not_test!(panic!("This should not panic"));
	}
}
