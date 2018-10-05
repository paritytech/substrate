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

//! API's for interfacing with the runtime via native/wasm.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate sr_std as rstd;
extern crate sr_primitives as primitives;
#[doc(hidden)]
pub extern crate parity_codec as codec;
extern crate sr_version as runtime_version;

#[doc(hidden)]
pub use primitives::{ApplyResult, traits::Block as BlockT, generic::BlockId};
use runtime_version::RuntimeVersion;
use rstd::vec::Vec;
#[doc(hidden)]
pub use rstd::slice;
#[doc(hidden)]
pub use codec::{Encode, Decode};

/// Declare the given API traits.
///
/// # Example:
///
/// ```nocompile
/// decl_apis!{
///     pub trait Test<Event> {
///         fn test<AccountId>(event: Event) -> AccountId;
///     }
/// }
/// ```
///
/// Will result in the following declaration:
///
/// ```nocompile
/// mod runtime {
///     pub trait Test<Event, AccountId> {
///         fn test(event: Event) -> AccountId;
///     }
/// }
///
/// pub trait Test<Block: BlockT, Event> {
///     type Error;
///     fn test<AccountId: Encode + Decode>(&self, at: &BlockId<Block>, event: Event) -> Result<Event, Self::Error>;
/// }
/// ```
///
/// The declarations generated in the `runtime` module will be used by `impl_apis!` for implementing
/// the traits for a runtime. The other declarations should be used for implementing the interface
/// in the client.
#[macro_export]
macro_rules! decl_apis {
	(
		$(
			$( #[$attr:meta] )*
			pub trait $name:ident $(< $( $generic_param:ident $( : $generic_bound:ident )* ),* >)* {
				$(
					fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
						$( $param_name:ident : $param_type:ty )*
					) $( -> $return_ty:ty)*;
				)*
			}
		)*
	) => {
		$(
			decl_apis!(
				@ADD_BLOCK_GENERIC
				$( #[$attr] )*
				pub trait $name $(< $( $generic_param $( : $generic_bound )* ),* >)* {
					$(
						fn $fn_name $( < $( $fn_generic ),* > )* ($( $param_name : $param_type )* ) $( -> $return_ty )*;
					)*
				};
				;
				;
				$( $( $generic_param $( : $generic_bound )* ),* )*
			);
		)*
		decl_apis! {
			@GENERATE_RUNTIME_TRAITS
			$(
				$( #[$attr] )*
				pub trait $name $(< $( $generic_param $( : $generic_bound )* ),* >)* {
					$(
						fn $fn_name $( < $( $fn_generic ),* > )* ($( $param_name : $param_type )* ) $( -> $return_ty )*;
					)*
				};
			)*
		}
	};
	(@ADD_BLOCK_GENERIC
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
		decl_apis!(
			@ADD_BLOCK_GENERIC
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$(
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type )*
					) $( -> $return_ty )*;
				)*
			};
			Found;
			$( $generic_param_parsed $( : $generic_bound_parsed )* , )* Block: $crate::BlockT;
			$( $generic_param_rest $( : $generic_bound_rest )* ),*
		);
	};
	(@ADD_BLOCK_GENERIC
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
	 		$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty )*;
			)*
		};
		$( $block_found:ident )*;
		$( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
		$generic_param:ident $( : $generic_bound:ident )*
		$(, $generic_param_rest:ident $( : $generic_bound_rest:ident )* )*
	) => {
		decl_apis!(
			@ADD_BLOCK_GENERIC
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
	(@ADD_BLOCK_GENERIC
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty )*;
			)*
		};
		Found;
	 	$( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
	) => {
		decl_apis!(
			@GENERATE_FNS
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
	(@ADD_BLOCK_GENERIC
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
		decl_apis!(
			@GENERATE_FNS
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$(
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type )*
					) $( -> $return_ty )*;
				)*
			};
			// We need to add the required generic Block parameter
			Block: $crate::BlockT $(, $generic_param_parsed $( : $generic_bound_parsed )* )*;
			{};
			$( $( $return_ty )*; )*
		);
	};
	(@GENERATE_FNS
        $( #[$attr:meta] )*
        pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty)*;
			)*
        };
        $( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
		{ $( $result_return_ty:ty; )* };
		$return_ty_current:ty;
		$( $( $return_ty_rest:ty )*; )*
	) => {
		decl_apis!(
			@GENERATE_FNS
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
	(@GENERATE_FNS
        $( #[$attr:meta] )*
        pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty)*;
			)*
        };
        $( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
		{ $( $result_return_ty:ty; )* };
		;
		$( $( $return_ty_rest:ty )*; )*
	) => {
		decl_apis!(
			@GENERATE_FNS
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
	(@GENERATE_FNS
        $( #[$attr:meta] )*
        pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty)*;
			)*
        };
        $( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
		{ $( $result_return_ty:ty; )* };
	) => {
		decl_apis!(
			@GENERATE_CLIENT_TRAITS
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
			$( $( $generic_param_orig $( : $generic_bound_orig )*, )* )* $( $( $( $fn_generic, )* )* )*;
		);
	};
	(@GENERATE_CLIENT_TRAITS
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$(
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty )*
				) $( -> $return_ty:ty)*;
			)*
		};
		$( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
		{ $( $result_return_ty:ty; )* };
		$( $generic_param_joined:ident $( : $generic_bound_joined:ident )*, )*;
	) => {
		$( #[$attr] )*
		pub trait $name < $( $generic_param_parsed $( : $generic_bound_parsed )* ),* > {
			type Error;

			$(
				fn $fn_name $( < $( $fn_generic: $crate::Encode + $crate::Decode ),* > )* (
					&self, at: &$crate::BlockId<Block> $(, $param_name: $param_type )*
				) -> $result_return_ty;
			)*
		}
	};
	(@GENERATE_RUNTIME_TRAITS
		$(
			$( #[$attr:meta] )*
			pub trait $name:ident $(< $( $generic_param:ident $( : $generic_bound:ident )* ),* >)* {
				$(
					fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
						$( $param_name:ident : $param_type:ty )*
					) $( -> $return_ty:ty)*;
				)*
			};
		)*
	) => {
		decl_apis! {
			@GENERATE_RUNTIME_TRAITS_WITH_JOINED_GENERICS
			$(
				$( #[$attr] )*
				pub trait $name < $( $( $generic_param $( : $generic_bound )*, )* )* $( $( $( $fn_generic, )* )* )* > {
					$(
						fn $fn_name ($( $param_name: $param_type ),*) $( -> $return_ty )*;
					)*
				}
			)*
		}
	};
	(@GENERATE_RUNTIME_TRAITS_WITH_JOINED_GENERICS
		$(
			$( #[$attr:meta] )*
			pub trait $name:ident < $( $generic_param:ident $( : $generic_bound:ident )*, )* > {
				$(
					fn $fn_name:ident($( $param_name:ident : $param_type:ty )*) $( -> $return_ty:ty)*;
				)*
			}
		)*
	) => {
		pub mod runtime {
			use super::*;

			$(
				$( #[$attr] )*
				pub trait $name < $( $generic_param $( : $generic_bound )* ),* > {
					$(
						fn $fn_name ($( $param_name: $param_type ),*) $( -> $return_ty )*;
					)*
				}
			)*
		}
	};
}

decl_apis! {
	/// The `Core` api trait that is mandantory for each runtime.
	pub trait Core<Block: BlockT, AuthorityId> {
		fn version() -> RuntimeVersion;
		fn authorities() -> Vec<AuthorityId>;
		fn execute_block(block: Block);
	}

	/// The `Metadata` api trait that returns metadata for the runtime.
	pub trait Metadata {
		fn metadata() -> Vec<u8>;
	}

	/// The `BlockBuilder` api trait that provides required functions for building a block for a runtime.
	pub trait BlockBuilder<Block: BlockT> {
		fn initialise_block(header: <Block as BlockT>::Header);
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyResult;
		fn finalise_block() -> <Block as BlockT>::Header;
		fn inherent_extrinsics<InherentExtrinsic, UncheckedExtrinsic>(inherent: InherentExtrinsic) -> Vec<UncheckedExtrinsic>;
		fn random_seed() -> <Block as BlockT>::Hash;
	}

	/// The `OldTxQueue` api trait for interfering with the old transaction queue.
	pub trait OldTxQueue {
		fn account_nonce<AccountId, Index>(account: AccountId) -> Index;
		fn lookup_address<Address, LookupId>(address: Address) -> Option<LookupId>;
	}

	/// The `NewTxQueue` api trait for interfering with the new transaction queue.
	pub trait NewTxQueue<Block: BlockT> {
		fn validate_transaction<TransactionValidity>(tx: <Block as BlockT>::Extrinsic) -> TransactionValidity;
	}

	/// The `Miscellaneous` api trait for getting miscellaneous information from the runtime.
	pub trait Miscellaneous {
		fn validator_count() -> u32;
		fn validators<AccountId>() -> Vec<AccountId>;
		fn timestamp<Moment>() -> Moment;
	}
}

/// Implement the given API's for the given runtime.
/// All desired API's need to be implemented in one `impl_apis!` call.
/// Besides generating the implementation for the runtime, there will be also generated an
/// auxiliary module named `api` that contains function for inferring with the API in native/wasm.
/// It is important to use the traits from the `runtime` module with this macro.
///
/// # Example:
///
/// ```nocompile
/// #[macro_use]
/// extern crate sr_api as runtime_api;
///
/// use runtime_api::runtime::{Core, OldTxQueue};
///
/// impl_apis! {
///     impl Core<Block, AccountId> for Runtime {
///         fn version() -> RuntimeVersion { 1 }
///         fn authorities() -> Vec<AuthorityId> { vec![1] }
///         fn execute_block(block: Block) {
///             //comment
///             let block = call_arbitrary_code(block);
///             execute(block);
///         }
///     }
///
///     impl OldTxQueue<AccountId, Index, Address, LookupId> for Runtime {
///         fn account_nonce(account: AccountId) -> Index {
///             0
///         }
///         fn lookup_address(address: Address) -> Option<LookupId> {
///             None
///         }
///     }
/// }
///
/// fn main() {}
/// ```
#[macro_export]
macro_rules! impl_apis {
	(
		impl $trait_name:ident $( < $( $generic:ident ),* > )* for $runtime:ident {
			$(
				fn $fn_name:ident ( $( $arg_name:ident : $arg_ty:ty ),* ) $( -> $return_ty:ty )* {
					$( $impl:tt )*
				}
			)*
		}
		$( $rest:tt )*
	) => {
		impl $trait_name $( < $( $generic ),* > )* for $runtime {
			$(
				fn $fn_name ( $( $arg_name : $arg_ty ),* ) $( -> $return_ty )* {
					$( $impl )*
				}
			)*
		}
		impl_apis! {
			$runtime;
			$( $fn_name ( $( $arg_name: $arg_ty ),* ); )*;
			$( $rest )*
		}
	};
	(
		$runtime:ident;
		$( $fn_name_parsed:ident ( $( $arg_name_parsed:ident : $arg_ty_parsed:ty ),* ); )*;
		impl $trait_name:ident $( < $( $generic:ident ),* > )* for $runtime_ignore:ident {
			$(
				fn $fn_name:ident ( $( $arg_name:ident : $arg_ty:ty ),* ) $( -> $return_ty:ty )* {
					$( $impl:tt )*
				}
			)*
		}
		$( $rest:tt )*
	) => {
		impl $trait_name $( < $( $generic ),* > )* for $runtime {
			$(
				fn $fn_name ( $( $arg_name : $arg_ty ),* ) $( -> $return_ty )* {
					$( $impl )*
				}
			)*
		}
		impl_apis! {
			$runtime;
			$( $fn_name_parsed ( $( $arg_name_parsed: $arg_ty_parsed )* ); )*
			$( $fn_name ( $( $arg_name: $arg_ty ),* ); )*;
			$( $rest )*
		}
	};
	(
		$runtime:ident;
		$( $fn_name:ident ( $( $arg_name:ident : $arg_ty:ty ),* ); )*;
	) => {
		pub mod api {
			use super::*;

			#[cfg(feature = "std")]
			pub fn dispatch(method: &str, mut data: &[u8]) -> Option<Vec<u8>> {
				match method {
					$(
						stringify!($fn_name) => {
							Some({impl_apis! {
								@GENERATE_IMPL_CALL
								$runtime;
								$fn_name;
								$( $arg_name : $arg_ty ),*;
								data;
							}})
						}
					)*
						_ => None,
				}
			}

			$(
				#[cfg(not(feature = "std"))]
				#[no_mangle]
				pub fn $fn_name(input_data: *mut u8, input_len: usize) -> u64 {
					let mut input = if input_len == 0 {
						&[0u8; 0]
					} else {
						unsafe {
							$crate::slice::from_raw_parts(input_data, input_len)
						}
					};

					let output = { impl_apis! {
						@GENERATE_IMPL_CALL
						$runtime;
						$fn_name;
						$( $arg_name : $arg_ty ),*;
						input;
					}};
					let res = output.as_ptr() as u64 + ((output.len() as u64) << 32);

					// Leak the output vector to avoid it being freed.
					// This is fine in a WASM context since the heap
					// will be discarded after the call.
					::core::mem::forget(output);
					res
				}
			)*
		}
	};
	(@GENERATE_IMPL_CALL
		$runtime:ident;
		$fn_name:ident;
		$arg_name:ident : $arg_ty:ty;
		$input:ident;
	) => {
		let $arg_name : $arg_ty = match $crate::codec::Decode::decode(&mut $input) {
			Some(input) => input,
			None => panic!("Bad input data provided to {}", stringify!($fn_name)),
		};

		let output = $runtime::$fn_name($arg_name);
		$crate::codec::Encode::encode(&output)
	};
	(@GENERATE_IMPL_CALL
		$runtime:ident;
		$fn_name:ident;
		$( $arg_name:ident : $arg_ty:ty ),*;
		$input:ident;
	) => {
		let ( $( $arg_name ),* ) : ($( $arg_ty ),*) = match $crate::codec::Decode::decode(&mut $input) {
			Some(input) => input,
			None => panic!("Bad input data provided to {}", stringify!($fn_name)),
		};

		let output = $runtime::$fn_name($( $arg_name ),*);
		$crate::codec::Encode::encode(&output)
	};
}
