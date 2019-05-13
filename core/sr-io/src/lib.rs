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

//! This is part of the Substrate runtime.

#![warn(missing_docs)]

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(lang_items))]
#![cfg_attr(not(feature = "std"), feature(alloc_error_handler))]
#![cfg_attr(not(feature = "std"), feature(core_intrinsics))]

#![cfg_attr(feature = "std", doc = "Substrate runtime standard library as compiled when linked with Rust's standard library.")]
#![cfg_attr(not(feature = "std"), doc = "Substrate's runtime standard library as compiled without Rust's standard library.")]

use hash_db::Hasher;
use rstd::vec::Vec;

#[doc(hidden)]
pub use codec;

pub use primitives::Blake2Hasher;

/// Error verifying ECDSA signature
pub enum EcdsaVerifyError {
	/// Incorrect value of R or S
	BadRS,
	/// Incorrect value of V
	BadV,
	/// Invalid signature
	BadSignature,
}

/// Trait for things which can be printed.
pub trait Printable {
	/// Print the object.
	fn print(self);
}

/// Converts a public trait definition into a private trait and set of public functions
/// that assume the trait is implemented for `()` for ease of calling.
macro_rules! export_api {
	(
		$( #[$trait_attr:meta] )*
		pub(crate) trait $trait_name:ident {
			$(
				$( #[$attr:meta] )*
				fn $name:ident
					$(< $( $g_name:ident $( : $g_ty:path )? ),+ >)?
					( $( $arg:ident : $arg_ty:ty ),* )
					$( -> $ret:ty )?
					$( where $( $w_name:path : $w_ty:path ),+ )?;
			)*
		}
	) => {
		$( #[$trait_attr] )*
		pub(crate) trait $trait_name {
			$(
				$( #[$attr] )*
				fn $name $(< $( $g_name $( : $g_ty )? ),+ >)? ( $($arg : $arg_ty ),* ) $( -> $ret )?
				$( where $( $w_name : $w_ty ),+ )?;
			)*
		}

		$(
			$( #[$attr] )*
			pub fn $name $(< $( $g_name $( : $g_ty )? ),+ >)? ( $($arg : $arg_ty ),* ) $( -> $ret )?
				$( where $( $w_name : $w_ty ),+ )?
			{
				#[allow(deprecated)]
				<()>:: $name $(::< $( $g_name ),+ > )?  ( $( $arg ),* )
			}
		)*
	}
}

export_api! {
	pub(crate) trait StorageApi {
		/// Get `key` from storage and return a `Vec`, empty if there's a problem.
		fn storage(key: &[u8]) -> Option<Vec<u8>>;

		/// Get `key` from child storage and return a `Vec`, empty if there's a problem.
		fn child_storage(storage_key: &[u8], key: &[u8]) -> Option<Vec<u8>>;

		/// Get `key` from storage, placing the value into `value_out` (as much of it as possible) and return
		/// the number of bytes that the entry in storage had beyond the offset or None if the storage entry
		/// doesn't exist at all. Note that if the buffer is smaller than the storage entry length, the returned
		/// number of bytes is not equal to the number of bytes written to the `value_out`.
		fn read_storage(key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize>;

		/// Get `key` from child storage, placing the value into `value_out` (as much of it as possible) and return
		/// the number of bytes that the entry in storage had beyond the offset or None if the storage entry
		/// doesn't exist at all. Note that if the buffer is smaller than the storage entry length, the returned
		/// number of bytes is not equal to the number of bytes written to the `value_out`.
		fn read_child_storage(storage_key: &[u8], key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize>;

		/// Set the storage of some particular key to Some value.
		fn set_storage(key: &[u8], value: &[u8]);

		/// Set the child storage of some particular key to Some value.
		fn set_child_storage(storage_key: &[u8], key: &[u8], value: &[u8]);

		/// Clear the storage of a key.
		fn clear_storage(key: &[u8]);

		/// Clear the storage of a key.
		fn clear_child_storage(storage_key: &[u8], key: &[u8]);

		/// Clear an entire child storage.
		fn kill_child_storage(storage_key: &[u8]);

		/// Check whether a given `key` exists in storage.
		fn exists_storage(key: &[u8]) -> bool;

		/// Check whether a given `key` exists in storage.
		fn exists_child_storage(storage_key: &[u8], key: &[u8]) -> bool;

		/// Clear the storage entries with a key that starts with the given prefix.
		fn clear_prefix(prefix: &[u8]);

		/// "Commit" all existing operations and compute the resultant storage root.
		fn storage_root() -> [u8; 32];

		/// "Commit" all existing operations and compute the resultant child storage root.
		fn child_storage_root(storage_key: &[u8]) -> Vec<u8>;

		/// "Commit" all existing operations and get the resultant storage change root.
		fn storage_changes_root(parent_hash: [u8; 32], parent_num: u64) -> Option<[u8; 32]>;

		/// A trie root formed from the enumerated items.
		/// TODO [#2382] remove (just use `ordered_trie_root` (NOTE currently not implemented for without_std))
		fn enumerated_trie_root<H>(input: &[&[u8]]) -> H::Out
		where
			H: Hasher,
			H: self::imp::HasherBounds,
			H::Out: Ord
		;

		/// A trie root formed from the iterated items.
		fn trie_root<H, I, A, B>(input: I) -> H::Out
		where
			I: IntoIterator<Item = (A, B)>,
			A: AsRef<[u8]>,
			A: Ord,
			B: AsRef<[u8]>,
			H: Hasher,
			H: self::imp::HasherBounds,
			H::Out: Ord
		;

		/// A trie root formed from the enumerated items.
		fn ordered_trie_root<H, I, A>(input: I) -> H::Out
		where
			I: IntoIterator<Item = A>,
			A: AsRef<[u8]>,
			H: Hasher,
			H: self::imp::HasherBounds,
			H::Out: Ord
		;
	}
}

export_api! {
	pub(crate) trait OtherApi {
		/// The current relay chain identifier.
		fn chain_id() -> u64;

		/// Print a printable value.
		fn print<T>(value: T)
		where
			T: Printable,
			T: Sized
		;
	}
}

export_api! {
	pub(crate) trait CryptoApi {
		/// Verify a ed25519 signature.
		fn ed25519_verify<P: AsRef<[u8]>>(sig: &[u8; 64], msg: &[u8], pubkey: P) -> bool;

		/// Verify an sr25519 signature.
		fn sr25519_verify<P: AsRef<[u8]>>(sig: &[u8; 64], msg: &[u8], pubkey: P) -> bool;

		/// Verify and recover a SECP256k1 ECDSA signature.
		/// - `sig` is passed in RSV format. V should be either 0/1 or 27/28.
		/// - returns `Err` if the signature is bad, otherwise the 64-byte pubkey (doesn't include the 0x04 prefix).
		fn secp256k1_ecdsa_recover(sig: &[u8; 65], msg: &[u8; 32]) -> Result<[u8; 64], EcdsaVerifyError>;
	}
}

export_api! {
	pub(crate) trait HashingApi {
		/// Conduct a 256-bit Keccak hash.
		fn keccak_256(data: &[u8]) -> [u8; 32] ;

		/// Conduct a 128-bit Blake2 hash.
		fn blake2_128(data: &[u8]) -> [u8; 16];

		/// Conduct a 256-bit Blake2 hash.
		fn blake2_256(data: &[u8]) -> [u8; 32];

		/// Conduct four XX hashes to give a 256-bit result.
		fn twox_256(data: &[u8]) -> [u8; 32];

		/// Conduct two XX hashes to give a 128-bit result.
		fn twox_128(data: &[u8]) -> [u8; 16];

		/// Conduct two XX hashes to give a 64-bit result.
		fn twox_64(data: &[u8]) -> [u8; 8];
	}
}

export_api! {
	pub(crate) trait OffchainApi {
		/// Submit extrinsic from the runtime.
		///
		/// Depending on the kind of extrinsic it will either be:
		/// 1. scheduled to be included in the next produced block (inherent)
		/// 2. added to the pool and propagated (transaction)
		fn submit_extrinsic<T: codec::Encode>(data: &T);
	}
}

/// API trait that should cover all other APIs.
///
/// Implement this to make sure you implement all APIs.
trait Api: StorageApi + OtherApi + CryptoApi + HashingApi + OffchainApi {}

mod imp {
	use super::*;

	#[cfg(feature = "std")]
	include!("../with_std.rs");

	#[cfg(not(feature = "std"))]
	include!("../without_std.rs");
}

#[cfg(feature = "std")]
pub use self::imp::{StorageOverlay, ChildrenStorageOverlay, with_storage, with_externalities, TestExternalities};
#[cfg(not(feature = "std"))]
pub use self::imp::ext::*;
