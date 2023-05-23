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

/// export the main pallet macro. This can wrap a `mod pallet` and will transform it into being
/// a pallet, eg `#[frame::pallet] mod pallet { .. }`.
pub use frame_support::pallet;

/// A prelude that is suitable to be used inside the
pub mod prelude {
	pub use super::macros::*;
	pub use frame_support::pallet_prelude::*;
	pub use frame_system::pallet_prelude::*;
}

/// All macros often used in FRAME pallets.
pub mod macros {
	pub use frame_support::{
		assert_err, assert_err_ignore_postinfo, assert_error_encoded_size, assert_noop, assert_ok,
		assert_storage_noop, defensive, defensive_assert, ensure, parameter_types, storage_alias,
	};
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

/// Testing-specific helpers.
#[cfg(feature = "std")]
pub mod testing {
	pub mod prelude {
		pub use frame_system::mocking::*;
		pub use sp_io::TestExternalities as TestState;
		// TODO: why are these not available in no-std?
		pub use sp_runtime::{bounded_btree_map, bounded_vec};
	}
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
	pub use frame_executive::*;
	pub use frame_support::{construct_runtime, OpaqueMetadata};
	pub use sp_api::impl_runtime_apis;
	pub use sp_inherents::{CheckInherentsResult, InherentData};
	pub use sp_runtime::{generic as bock_types_generic, ApplyExtrinsicResult};
	#[cfg(feature = "std")] // TODO: can be removed once we are done with native runtime.
	pub use sp_version::NativeVersion;
	pub use sp_version::{create_runtime_str, runtime_version, RuntimeVersion};
	/// A set of opinionated types aliases commonly used in runtimes.
	pub mod runtime_types_common {
		pub type BlockNumber = u32;
		// If you mistakenly change this to u32, but don't update it in all places, you will suffer.
		pub type Index = ();
		/// 32 byte account id. Consider using [`sp_runtime::MultiSigner`] if you are interested
		/// supporting various size account ids.
		pub type AccountId = <<Signature as sp_runtime::traits::Verify>::Signer as sp_runtime::traits::IdentifyAccount>::AccountId;
		pub type Signature = sp_runtime::MultiSignature;
		// TODO: I really prefer these default to not be any type of multi-* and just be a simple
		// 32, ed25519 byte account id and signature.
		pub type Address = sp_runtime::MultiAddress<AccountId, Index>;
		pub type Header = sp_runtime::generic::Header<BlockNumber, sp_runtime::traits::BlakeTwo256>;
		pub type Extrinsic<RuntimeCall, Extra = ()> =
			sp_runtime::generic::UncheckedExtrinsic<Address, RuntimeCall, Signature, Extra>;
		pub type BlockOf<RuntimeCall, Extra = ()> =
			sp_runtime::generic::Block<Header, Extrinsic<RuntimeCall, Extra>>;

		pub type ExtrinsicOf<Block> = <Block as sp_runtime::traits::Block>::Extrinsic;
		pub type HeaderOf<Block> = <Block as sp_runtime::traits::Block>::Header;
	}

	pub mod runtime_types_generic {
		pub use sp_runtime::{
			generic::*, AccountId32, MultiAddress, MultiSignature, MultiSigner, OpaqueExtrinsic,
		};
	}

	pub mod runtime_apis {
		// TODO: preferably not do wildcard imports, but we need to bring in some macro_generated
		// stuff.
		pub use sp_api::{self, *};
		pub use sp_block_builder::*;
		pub use sp_consensus_aura::*;
		pub use sp_consensus_grandpa::*;
		pub use sp_offchain::*;
		pub use sp_transaction_pool::runtime_api::*;
	}

	/// The two database types that can be used, and their corresponding weights.
	pub mod db_weights {
		pub use frame_support::weights::constants::{ParityDbWeight, RocksDbWeight};
	}

	/// All weight-related types.
	pub use frame_support::weights;
}

/// Substrate's specific `std` library. See [`deps::sp_std`].
pub use sp_std as std;

/// A macro-sub module that contains a list of all pallet macros, with proper documentation. It
/// enhances IDE experience.
// TODO: does not seem to work.
pub use frame_support::pallet_macros as pallet;

/// Access to all of the dependencies of this crate. In case the re-exports are not enough, this
/// module can be used.
pub mod deps {
	pub use frame_support;
	pub use frame_system;
	pub use parity_scale_codec;
	pub use scale_info;
	pub use sp_arithmetic;
	pub use sp_core;
	pub use sp_runtime;
	pub use sp_std;

	#[cfg(feature = "runtime")]
	pub use frame_executive;
	#[cfg(feature = "runtime")]
	pub use sp_api;
	#[cfg(feature = "runtime")]
	pub use sp_version;
}
