//! # FRAME
//!
//! > Substrate's State Transition Function (Runtime) Framework.
//!
//!   ______   ______    ________   ___ __ __   ______
//!  /_____/\ /_____/\  /_______/\ /__//_//_/\ /_____/\
//!  \::::_\/_\:::_ \ \ \::: _  \ \\::\| \| \ \\::::_\/_
//!   \:\/___/\\:(_) ) )_\::(_)  \ \\:.      \ \\:\/___/\
//!    \:::._\/ \: __ `\ \\:: __  \ \\:.\-/\  \ \\::___\/_
//!     \:\ \    \ \ `\ \ \\:.\ \  \ \\. \  \  \ \\:\____/\
//!      \_\/     \_\/ \_\/ \__\/\__\/ \__\/ \__\/ \_____\/
//!
//!
//! # Introduction
//!
//! Substrate is at a very high level composed of two parts:
//!
//! 1. A *runtime* who's representing the state transition function of a blockchain, and is encoded
//! as a wasm blob.
//! 2. A client' who's primary purpose is to execute the given runtime.
//!
//! FRAME is the primary framework to build a runtime.
//!
//! ## Pallets
//!
//! ```
//! use frame::pallet;
//!
//! #[pallet::pallet]
//! mod pallet {
//!
//! 	#[pallet::config]
//! 	pub trait Config: frame_system::Config {}
//!
//! 	#[pallet::pallet]
//! 	pub struct Pallet<T>(_);
//! }
//! # fn main() {}
//! ```
//!
//! ## Runtime
//!
//! <TODO>
//!
//! # This Crate
//!
//! This crate is an amalgamation of multiple other crates that are often used together to compose a
//! pallet. It is not necessary to use it, and it may fall short for certain purposes.
//!
//! In short, this crate only re-exports types and traits from multiple sources. All of these
//! sources are listed (and re-exported again) in [`deps`].

#![cfg_attr(not(feature = "std"), no_std)]

/// export the main pallet macro. This can wrap a `mod pallet` and will transform it into being
/// a pallet, eg `#[frame::pallet] mod pallet { .. }`.
pub use frame_support::pallet;

/// A macro-sub module that contains a list of all pallet macros, with proper documentation. It
/// enhances IDE experience.
pub use frame_support::pallet_macros as _;

pub mod prelude {
	pub use frame_support::pallet_prelude::*;
	pub use frame_system::{self, pallet_prelude::*};
	pub use sp_std::prelude::*;
}

#[cfg(feature = "std")]
pub mod testing_prelude {
	#[cfg(feature = "runtime")]
	pub use super::runtime::testing_prelude::*;

	pub use frame_support::{
		assert_err, assert_err_ignore_postinfo, assert_error_encoded_size, assert_noop, assert_ok,
		assert_storage_noop, derive_impl, ord_parameter_types, parameter_types,
		parameter_types_impl_thread_local, storage_alias,
	};
	pub use frame_system::mocking::*;
	pub use sp_io::TestExternalities as TestState;
}

pub mod macros {
	pub use frame_support::{derive_impl, macro_magic::use_attr, register_default_impl};
	pub use sp_std::if_std;
}

/// All traits often used in FRAME pallets.
///
/// Note that types implementing these traits can also be found in this module.
pub mod traits {
	pub use frame_support::traits::*;
	pub use sp_runtime::traits::*;
}

/// The arithmetic types used for safe math.
pub mod arithmetic {
	pub use sp_arithmetic::{traits::*, *};
}

/// Low level primitive types used in FRAME pallets.
pub mod primitives {
	pub use sp_core::{H160, H256, H512, U256, U512};
	pub use sp_runtime::traits::{BlakeTwo256, Hash, Keccak256};
}

/// All derive macros.
pub mod derive {
	pub use frame_support::{
		CloneNoBound, DebugNoBound, DefaultNoBound, EqNoBound, PartialEqNoBound,
		RuntimeDebugNoBound,
	};
	pub use parity_scale_codec::{Decode, Encode};
	pub use scale_info::TypeInfo;
	pub use sp_std::fmt::Debug;
}

/// types that are often needed to amalgamate a real runtime. In principle, this is very similar to
/// [`test`], but it contains production-ready types, as opposed to mocks.
#[cfg(feature = "runtime")]
pub mod runtime {
	pub mod prelude {
		pub use frame_executive::*;
		pub use frame_support::{construct_runtime, derive_impl, parameter_types, OpaqueMetadata};
		pub use sp_api::impl_runtime_apis;
		pub use sp_inherents::{CheckInherentsResult, InherentData};
		pub use sp_runtime::{generic as block_types_generic, ApplyExtrinsicResult};
		#[cfg(feature = "std")]
		pub use sp_version::NativeVersion;
		pub use sp_version::{create_runtime_str, runtime_version, RuntimeVersion};
	}

	#[cfg(feature = "std")]
	pub mod testing_prelude {
		pub use frame_support::construct_runtime;
		pub use sp_core::storage::Storage;
		pub use sp_runtime::BuildStorage;
	}

	/// A set of opinionated types aliases commonly used in runtimes.
	///
	/// This is one set of opinionated types. They are compatible with one another, but are not
	/// guaranteed to work if you start tweaking a portion.
	///
	/// Some note-worthy opinions in this prelude:
	///
	/// - [`sp_runtime::MultiAddress`] and [`sp_runtime::MultiSignature`] are used as the account id
	///   and signature types. This implies that this prelude can possibly used with an
	///   "account-index" system (eg `pallet-indices`). And, in any case, it should be paired with
	///   [`AccountIdLookup`] in [`frame_system::Config::Lookup`].
	/// - The choice of hashing, blocknumber, account account nonce are left to
	///   [`frame_system::Config`]. Set these values with care.
	// TODO: tests that this works for multiple ones.
	// TODO: a prelude that works with `AccountId32`.
	pub mod runtime_types_common {
		use frame_system::Config as SysConfig;

		/// A signature type compatible capably of handling multiple crypto-schemes.
		pub type Signature = sp_runtime::MultiSignature;

		/// The corresponding account-id type of [`Signature`].
		pub type AccountId = <
			<Signature as sp_runtime::traits::Verify>::Signer
			as
			sp_runtime::traits::IdentifyAccount
		>::AccountId;

		type HeaderInner<T> =
			sp_runtime::generic::Header<BlockNumberOf<T>, <T as SysConfig>::Hashing>;

		// NOTE: `AccountIndex` is provided for future compatibility, if you want to introduce
		// something like `pallet-indices`.
		type ExtrinsicInner<T, Extra, AccountIndex = ()> = sp_runtime::generic::UncheckedExtrinsic<
			sp_runtime::MultiAddress<AccountId, AccountIndex>,
			<T as SysConfig>::RuntimeCall,
			Signature,
			Extra,
		>;

		pub type SystemSignedExtensionsOf<T> = (
			frame_system::CheckNonZeroSender<T>,
			frame_system::CheckSpecVersion<T>,
			frame_system::CheckTxVersion<T>,
			frame_system::CheckGenesis<T>,
			frame_system::CheckEra<T>,
			frame_system::CheckNonce<T>,
			frame_system::CheckWeight<T>,
		);

		/// The block type.
		///
		/// Should be parameterized with `T: frame_system::Config` and a tuple of `SignedExtension`.
		/// When in doubt, use [`SystemSignedExtensionsOf`].
		pub type BlockOf<T, Extra = ()> =
			sp_runtime::generic::Block<HeaderInner<T>, ExtrinsicInner<T, Extra>>;

		/// The opaque block type. This is the same [`BlockOf`], but it has
		/// [`sp_runtime::OpaqueExtrinsic`] as its final extrinsic type. This should be provided to
		/// the client side as the extrinsic type.
		pub type OpaqueBlockOf<T> =
			sp_runtime::generic::Block<HeaderInner<T>, sp_runtime::OpaqueExtrinsic>;

		/// Get the extrinsic type from a decorated [`BlockOf`].
		pub type ExtrinsicOf<Block> = <Block as sp_runtime::traits::Block>::Extrinsic;

		/// Get the header type from a decorated [`BlockOf`].
		pub type HeaderOf<Block> = <Block as sp_runtime::traits::Block>::Header;

		/// The block number type to be used, as defined in [`frame_system::Config`].
		pub type BlockNumberOf<T> = <T as SysConfig>::BlockNumber;

		/// The account nonce type to be used, as defined in [`frame_system::Config`].
		pub type NonceOf<T> = <T as SysConfig>::Index;
	}

	pub mod runtime_types_generic {
		pub use sp_runtime::{
			generic::*, AccountId32, MultiAddress, MultiSignature, MultiSigner, OpaqueExtrinsic,
		};
	}

	pub mod runtime_apis {
		// This should contain all RPCs, but only those that are needed in order to run a bare-bone
		// chain.

		// TODO: preferably not do wildcard imports, but we need to bring in some macro_generated
		// stuff.
		pub use frame_system_rpc_runtime_api::*;
		pub use sp_api::{self, *};
		pub use sp_block_builder::*;
		pub use sp_consensus_aura::*;
		pub use sp_consensus_grandpa::*;
		pub use sp_offchain::*;
		pub use sp_session::api::*;
		pub use sp_transaction_pool::runtime_api::*;
	}

	/// The two database types that can be used, and their corresponding weights.
	pub mod db_weights {
		pub use frame_support::weights::constants::{ParityDbWeight, RocksDbWeight};
	}

	/// All weight-related types.
	pub use frame_support::weights;
}

/// Access to all of the dependencies of this crate. In case the re-exports are not enough, this
/// module can be used.
pub mod deps {
	// TODO: It would be great to somehow instruct RA to prefer *not* suggesting auto-imports from
	// these. For example, we prefer `frame::derive::CloneNoBound` rather than
	// `frame::deps::CloneNoBound`.
	pub use frame_support;
	pub use frame_system;
	pub use sp_arithmetic;
	pub use sp_core;
	pub use sp_runtime;
	pub use sp_std;

	pub use parity_scale_codec as codec;
	pub use scale_info;

	#[cfg(feature = "runtime")]
	pub use frame_executive;
	#[cfg(feature = "runtime")]
	pub use sp_api;
	#[cfg(feature = "runtime")]
	pub use sp_version;
}
