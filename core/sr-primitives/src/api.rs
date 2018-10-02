// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Primitives for interfacing with the runtime.

use {ApplyResult, traits::Block as BlockT, generic::BlockId};
use runtime_version::RuntimeVersion;
use rstd::vec::Vec;
use codec::{Encode, Decode};

macro_rules! decl_api {
	(
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param:ident $( : $generic_bound:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty)*;
			)*
		}
	) => {
		decl_api!(
			@add_block_generic
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param $( : $generic_bound )* ),* >)* {
				$(
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type )* ) $( -> $return_ty
					)*;
				)*
			};
			;
			;
			$( $( $generic_param $( : $generic_bound )* ),* )*
		);
	};
	(@add_block_generic
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty)*;
			)*
		};
		;
		$( $generic_param_parsed:ident $( : $generic_bound_parsed:ident )* ),*;
		Block: BlockT
		$(, $generic_param_rest:ident $( : $generic_bound_rest:ident )* )*
	) => {
		decl_api!(
			@add_block_generic
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$(
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type )*
					) $( -> $return_ty )*;
				)*
			};
			Found;
			$( $generic_param_parsed $( : $generic_bound_parsed )* , )* Block: BlockT;
			$( $generic_param_rest $( : $generic_bound_rest )* ),*
		);
	};
	(@add_block_generic
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
	 		$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty )*;
			)*
		};
		$( $block_found:ident )*;
		$( $generic_param_parsed:ident $( : $generic_bound_parsed:ident )* ),*;
		$generic_param:ident $( : $generic_bound:ident )*
		$(, $generic_param_rest:ident $( : $generic_bound_rest:ident )* )*
	) => {
		decl_api!(
			@add_block_generic
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$(
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type )*
					) $( -> $return_ty )*;
				)*
			};
			$( $block_found )*;
			$( $generic_param_parsed $( : $generic_bound_parsed )* , )* $generic_param $( : $generic_bound )*;
			$( $generic_param_rest $( : $generic_bound_rest )* ),*
		);
	};
	(@add_block_generic
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty )*;
			)*
		};
		Found;
	 	$( $generic_param_parsed:ident $( : $generic_bound_parsed:ident )* ),*;
	) => {
		decl_api!(
			@generate_fns
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$(
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type )*
					) $( -> $return_ty )*;
				)*
			};
			$( $generic_param_parsed $( : $generic_bound_parsed )* ),*;
			{};
			$( $( $return_ty )*; )*
		);
	};
	(@add_block_generic
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty )*;
			)*
		};
		;
		$( $generic_param_parsed:ident $( : $generic_bound_parsed:ident )* ),*;
	) => {
		decl_api!(
			@generate_fns
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$(
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type )*
					) $( -> $return_ty )*;
				)*
			};
			// We need to add the required generic Block parameter
			Block: BlockT $(, $generic_param_parsed $( : $generic_bound_parsed )* )*;
			{};
			$( $( $return_ty )*; )*
		);
	};
	(@generate_fns
        $( #[$attr:meta] )*
        pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty)*;
			)*
        };
        $( $generic_param_parsed:ident $( : $generic_bound_parsed:ident )* ),*;
		{ $( $result_return_ty:ty; )* };
		$return_ty_current:ty;
		$( $( $return_ty_rest:ty )*; )*
	) => {
		decl_api!(
			@generate_fns
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$(
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type )*
					) $( -> $return_ty )*;
				)*
			};
			$( $generic_param_parsed $( : $generic_bound_parsed )* ),*;
			{ $( $result_return_ty; )* Result<$return_ty_current, Self::Error>; };
			$( $( $return_ty_rest )*; )*
		);
	};
	(@generate_fns
        $( #[$attr:meta] )*
        pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty)*;
			)*
        };
        $( $generic_param_parsed:ident $( : $generic_bound_parsed:ident )* ),*;
		{ $( $result_return_ty:ty; )* };
		;
		$( $( $return_ty_rest:ty )*; )*
	) => {
		decl_api!(
			@generate_fns
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$(
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type )*
					) $( -> $return_ty )*;
				)*
			};
			$( $generic_param_parsed $( : $generic_bound_parsed )* ),*;
			{ $( $result_return_ty; )* Result<(), Self::Error>; };
			$( $( $return_ty_rest )*; )*
		);
	};
	(@generate_fns
        $( #[$attr:meta] )*
        pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty)*;
			)*
        };
        $( $generic_param_parsed:ident $( : $generic_bound_parsed:ident )* ),*;
		{ $( $result_return_ty:ty; )* };
	) => {
		decl_api!(
			@generate_traits
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$(
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type )*
					) $( -> $return_ty )*;
				)*
			};
			$( $generic_param_parsed $( : $generic_bound_parsed )* ),*;
			{ $( $result_return_ty; )* };
		);
	};
	(@generate_traits
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty)*;
			)*
		};
		$( $generic_param_parsed:ident $( : $generic_bound_parsed:ident )* ),*;
		{ $( $result_return_ty:ty; )* };
	) => {
		#[cfg(not(feature = "api-for-runtime"))]
		$( #[$attr] )*
		pub trait $name < $( $generic_param_parsed $( : $generic_bound_parsed )* ),* > {
			type Error;

			$(
				fn $fn_name $( < $( $fn_generic: Encode + Decode ),* > )* (
					&self, at: &BlockId<Block> $(, $param_name: $param_type )*
				) -> $result_return_ty;
			)*
		}

		#[cfg(feature = "api-for-runtime")]
		$( #[$attr] )*
		pub trait $name $( < $( $generic_param_orig $( : $generic_bound_orig )* ),* > )* {
			$(
				fn $fn_name $( < $( $fn_generic: Encode + Decode ),* > )* (
					$( $param_name: $param_type ),*
				) $( -> $return_ty )*;
			)*
		}
	};
}

decl_api! {
	/// The `Core` api trait that is mandantory for each runtime.
	pub trait Core<Block: BlockT, AuthorityId> {
		fn version() -> RuntimeVersion;
		fn authorities() -> Vec<AuthorityId>;
		fn execute_block(block: Block);
	}
}

decl_api! {
	/// The `Metadata` api trait that returns metadata for the runtime.
	pub trait Metadata {
		fn metadata() -> Vec<u8>;
	}
}

decl_api! {
	/// The `BlockBuilder` api trait that provides required functions for building a block for a runtime.
	pub trait BlockBuilder<Block: BlockT> {
		fn initialise_block(header: &<Block as BlockT>::Header);
		fn apply_extrinsic<Extrinsic>(extrinsic: &Extrinsic) -> ApplyResult;
		fn finalise_block() -> <Block as BlockT>::Header;
		fn inherent_extrinsics<InherentExtrinsic, UncheckedExtrinsic>(inherent: &InherentExtrinsic) -> Vec<UncheckedExtrinsic>;
		fn random_seed() -> <Block as BlockT>::Hash;
	}
}

decl_api! {
	/// The `OldTxQueue` api trait for interfering with the old transaction queue.
	pub trait OldTxQueue {
		fn account_nonce<AccountId, Index>(account: AccountId) -> Index;
		fn lookup_address<Address, AccountId>(address: Address) -> Option<AccountId>;
	}
}

decl_api! {
	/// The `NewTxQueue` api trait for interfering with the new transaction queue.
	pub trait NewTxQueue {
		fn validate_transaction<Extrinsic, TransactionValidity>(tx: Extrinsic) -> TransactionValidity;
	}
}

decl_api! {
	/// The `Miscellaneous` api trait for getting miscellaneous information from the runtime.
	pub trait Miscellaneous {
		fn validator_count() -> u32;
		fn validators<AccountId>() -> Vec<AccountId>;
		fn timestamp<Moment>() -> Moment;
	}
}
