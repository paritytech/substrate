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

//! Macros for declaring and implementing the runtime API's.

/// Declare the given API traits.
///
/// # Example:
///
/// ```nocompile
/// decl_runtime_apis!{
///     pub trait Test<Event> ExtraClientSide<ClientArg> {
///         fn test<AccountId>(event: Event) -> AccountId;
///
///         /// A function that will have the extra parameter `param` on the client side,
///         /// the runtime does not have any parameter.
///         fn testWithExtraParams() ExtraClientSide(param: &Self::ClientArg);
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
///     type ClientArg;
///     fn test<AccountId: Encode + Decode>(&self, at: &BlockId<Block>, event: Event) -> Result<Event, Self::Error>;
///     fn testWithExtraParams(&self, at: &BlockId<Block>, param: &Client) -> Result<Event, Self::Error>;
/// }
/// ```
///
/// The declarations generated in the `runtime` module will be used by `impl_runtime_apis!` for implementing
/// the traits for a runtime. The other declarations should be used for implementing the interface
/// in the client.
#[macro_export]
macro_rules! decl_runtime_apis {
	(
		$(
			$( #[$attr:meta] )*
			pub trait $name:ident $(< $( $generic_param:ident $( : $generic_bound:ident )* ),* >)*
				$( ExtraClientSide < $( $client_generic_param:ident $( : $client_generic_bound:ident )* ),+ > )*
			{
				$(
					$( #[$fn_attr:meta] )*
					fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
						$( $param_name:ident : $param_type:ty ),*
					)
					$( ExtraClientSide ( $( $client_param_name:ident : $client_param_type:ty ),+ ) )*
					$( -> $return_ty:ty)*;
				)*
			}
		)*
	) => {
		$(
			decl_runtime_apis!(
				@ADD_BLOCK_GENERIC
				$( #[$attr] )*
				pub trait $name $(< $( $generic_param $( : $generic_bound )* ),* >)* {
					$( $( type $client_generic_param $( : $client_generic_bound )*; )* )*
					$(
						$( #[$fn_attr] )*
						fn $fn_name $( < $( $fn_generic ),* > )* (
							$( $( $client_param_name: $client_param_type, )* )*
							$( $param_name : &$param_type, )*
						) $( -> $return_ty )*;
					)*
				};
				;
				;
				$( $( $generic_param $( : $generic_bound )* ),* )*
			);
		)*
		decl_runtime_apis! {
			@GENERATE_RUNTIME_TRAITS
			$(
				$( #[$attr] )*
				pub trait $name $(< $( $generic_param $( : $generic_bound )* ),* >)* {
					$(
						$( #[$fn_attr] )*
						fn $fn_name $( < $( $fn_generic ),* > )* ($( $param_name : $param_type )* ) $( -> $return_ty )*;
					)*
				};
			)*
		}
	};
	(@ADD_BLOCK_GENERIC
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$( type $client_generic_param:ident $( : $client_generic_bound:ident )*; )*
			$(
				$( #[$fn_attr:meta] )*
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty, )*
				) $( -> $return_ty:ty)*;
			)*
		};
		;
		$( $generic_param_parsed:ident $( : $generic_bound_parsed:ident )* ),*;
		Block: BlockT
		$(, $generic_param_rest:ident $( : $generic_bound_rest:ident )* )*
	) => {
		decl_runtime_apis!(
			@ADD_BLOCK_GENERIC
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$( type $client_generic_param $( : $client_generic_bound )*; )*
				$(
					$( #[$fn_attr] )*
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type, )*
					) $( -> $return_ty )*;
				)*
			};
			Found;
			$( $generic_param_parsed $( : $generic_bound_parsed )* , )* Block: $crate::runtime_api::BlockT;
			$( $generic_param_rest $( : $generic_bound_rest )* ),*
		);
	};
	(@ADD_BLOCK_GENERIC
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$( type $client_generic_param:ident $( : $client_generic_bound:ident )*; )*
	 		$(
				$( #[$fn_attr:meta] )*
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty, )*
				) $( -> $return_ty:ty )*;
			)*
		};
		$( $block_found:ident )*;
		$( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
		$generic_param:ident $( : $generic_bound:ident )*
		$(, $generic_param_rest:ident $( : $generic_bound_rest:ident )* )*
	) => {
		decl_runtime_apis!(
			@ADD_BLOCK_GENERIC
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$( type $client_generic_param $( : $client_generic_bound )*; )*
				$(
					$( #[$fn_attr] )*
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type, )*
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
			$( type $client_generic_param:ident $( : $client_generic_bound:ident )*; )*
			$(
				$( #[$fn_attr:meta] )*
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty, )*
				) $( -> $return_ty:ty )*;
			)*
		};
		Found;
	 	$( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
	) => {
		decl_runtime_apis!(
			@GENERATE_RETURN_TYPES
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$( type $client_generic_param $( : $client_generic_bound )*; )*
				$(
					$( #[$fn_attr] )*
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type, )*
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
			$( type $client_generic_param:ident $( : $client_generic_bound:ident )*; )*
			$(
				$( #[$fn_attr:meta] )*
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty, )*
				) $( -> $return_ty:ty )*;
			)*
		};
		;
		$( $generic_param_parsed:ident $( : $generic_bound_parsed:ident )* ),*;
	) => {
		decl_runtime_apis!(
			@GENERATE_RETURN_TYPES
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$( type $client_generic_param $( : $client_generic_bound )*; )*
				$(
					$( #[$fn_attr] )*
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type, )*
					) $( -> $return_ty )*;
				)*
			};
			// We need to add the required generic Block parameter
			Block: $crate::runtime_api::BlockT $(, $generic_param_parsed $( : $generic_bound_parsed )* )*;
			{};
			$( $( $return_ty )*; )*
		);
	};
	(@GENERATE_RETURN_TYPES
        $( #[$attr:meta] )*
        pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$( type $client_generic_param:ident $( : $client_generic_bound:ident )*; )*
			$(
				$( #[$fn_attr:meta] )*
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty, )*
				) $( -> $return_ty:ty)*;
			)*
        };
        $( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
		{ $( $result_return_ty:ty; )* };
		$return_ty_current:ty;
		$( $( $return_ty_rest:ty )*; )*
	) => {
		decl_runtime_apis!(
			@GENERATE_RETURN_TYPES
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$( type $client_generic_param $( : $client_generic_bound )*; )*
				$(
					$( #[$fn_attr] )*
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type, )*
					) $( -> $return_ty )*;
				)*
			};
			$( $generic_param_parsed $( : $generic_bound_parsed )* ),*;
			{ $( $result_return_ty; )* $crate::error::Result<$return_ty_current>; };
			$( $( $return_ty_rest )*; )*
		);
	};
	(@GENERATE_RETURN_TYPES
        $( #[$attr:meta] )*
        pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$( type $client_generic_param:ident $( : $client_generic_bound:ident )*; )*
			$(
				$( #[$fn_attr:meta] )*
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty, )*
				) $( -> $return_ty:ty)*;
			)*
        };
        $( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
		{ $( $result_return_ty:ty; )* };
		;
		$( $( $return_ty_rest:ty )*; )*
	) => {
		decl_runtime_apis!(
			@GENERATE_RETURN_TYPES
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$( type $client_generic_param $( : $client_generic_bound )*; )*
				$(
					$( #[$fn_attr] )*
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type, )*
					) $( -> $return_ty )*;
				)*
			};
			$( $generic_param_parsed $( : $generic_bound_parsed )* ),*;
			{ $( $result_return_ty; )* $crate::error::Result<()>; };
			$( $( $return_ty_rest )*; )*
		);
	};
	(@GENERATE_RETURN_TYPES
        $( #[$attr:meta] )*
        pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$( type $client_generic_param:ident $( : $client_generic_bound:ident )*; )*
			$(
				$( #[$fn_attr:meta] )*
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty, )*
				) $( -> $return_ty:ty)*;
			)*
        };
        $( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
		{ $( $result_return_ty:ty; )* };
	) => {
		decl_runtime_apis!(
			@GENERATE_CLIENT_TRAITS
			$( #[$attr] )*
			pub trait $name $(< $( $generic_param_orig $( : $generic_bound_orig )* ),* >)* {
				$( type $client_generic_param $( : $client_generic_bound )*; )*
				$(
					$( #[$fn_attr] )*
					fn $fn_name $( < $( $fn_generic ),* > )* (
						$( $param_name : $param_type, )*
					) $( -> $return_ty )*;
				)*
			};
			$( $generic_param_parsed $( : $generic_bound_parsed )* ),*;
			{ $( $result_return_ty; )* };
		);
	};
	(@GENERATE_CLIENT_TRAITS
		$( #[$attr:meta] )*
		pub trait $name:ident $(< $( $generic_param_orig:ident $( : $generic_bound_orig:ident )* ),* >)* {
			$( type $client_generic_param:ident $( : $client_generic_bound:ident )*; )*
			$(
				$( #[$fn_attr:meta] )*
				fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
					$( $param_name:ident : $param_type:ty, )*
				) $( -> $return_ty:ty)*;
			)*
		};
		$( $generic_param_parsed:ident $( : $generic_bound_parsed:path )* ),*;
		{ $( $result_return_ty:ty; )* };
	) => {
		$( #[$attr] )*
		pub trait $name < $( $generic_param_parsed $( : $generic_bound_parsed )* ),* > : $crate::runtime_api::Core<Block> {
			$( type $client_generic_param $( : $client_generic_bound )*; )*

			$(
				$( #[$fn_attr] )*
				fn $fn_name $( < $( $fn_generic: $crate::runtime_api::Encode + $crate::runtime_api::Decode ),* > )* (
					&self, at: &$crate::runtime_api::BlockId<Block> $(, $param_name: $param_type )*
				) -> $result_return_ty;
			)*
		}
	};
	(@GENERATE_RUNTIME_TRAITS
		$(
			$( #[$attr:meta] )*
			pub trait $name:ident $(< $( $generic_param:ident $( : $generic_bound:ident )* ),* >)* {
				$(
					$( #[$fn_attr:meta] )*
					fn $fn_name:ident $( < $( $fn_generic:ident ),* > )* (
						$( $param_name:ident : $param_type:ty )*
					) $( -> $return_ty:ty)*;
				)*
			};
		)*
	) => {
		decl_runtime_apis! {
			@GENERATE_RUNTIME_TRAITS_WITH_JOINED_GENERICS
			$(
				$( #[$attr] )*
				pub trait $name < $( $( $generic_param $( : $generic_bound )*, )* )* $( $( $( $fn_generic, )* )* )* > {
					$(
						$( #[$fn_attr] )*
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
					$( #[$fn_attr:meta] )*
					fn $fn_name:ident($( $param_name:ident : $param_type:ty ),*) $( -> $return_ty:ty)*;
				)*
			}
		)*
	) => {
		/// The API traits to implement on the runtime side.
		pub mod runtime {
			use super::*;

			$(
				$( #[$attr] )*
				pub trait $name < $( $generic_param $( : $generic_bound )* ),* > {
					$(
						$( #[$fn_attr] )*
						fn $fn_name ($( $param_name: $param_type ),*) $( -> $return_ty )*;
					)*
				}
			)*
		}
	};
}

/// Implement the given API's for the given runtime.
/// All desired API's need to be implemented in one `impl_runtime_apis!` call.
/// Besides generating the implementation for the runtime, there will be also generated an
/// auxiliary module named `api` that contains function for inferring with the API in native/wasm.
/// It is important to use the traits from the `runtime` module with this macro.
///
/// # Example:
///
/// ```nocompile
/// #[macro_use]
/// extern crate substrate_client as client;
///
/// use client::runtime_api::runtime::{Core, TaggedTransactionQueue};
///
/// impl_runtime_apis! {
///     impl Core<Block> for Runtime {
///         fn version() -> RuntimeVersion { unimplemented!() }
///         fn authorities() -> Vec<AuthorityId> { unimplemented!() }
///         fn execute_block(block: Block) {
///             //comment
///             unimplemented!()
///         }
///     }
///
///     impl TaggedTransactionQueue<Block> for Runtime {
///			fn validate_transaction(tx: <Block as BlockT>::Extrinsic) -> TransactionValidity {
///				unimplemented!()
///			}
///     }
/// }
///
/// fn main() {}
/// ```
#[macro_export]
macro_rules! impl_runtime_apis {
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
		impl_runtime_apis! {
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
		impl_runtime_apis! {
			$runtime;
			$( $fn_name_parsed ( $( $arg_name_parsed: $arg_ty_parsed ),* ); )*
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
							Some({impl_runtime_apis! {
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
							$crate::runtime_api::slice::from_raw_parts(input_data, input_len)
						}
					};

					let output = { impl_runtime_apis! {
						@GENERATE_IMPL_CALL
						$runtime;
						$fn_name;
						$( $arg_name : $arg_ty ),*;
						input;
					} };
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
		let $arg_name : $arg_ty = match $crate::runtime_api::Decode::decode(&mut $input) {
			Some(input) => input,
			None => panic!("Bad input data provided to {}", stringify!($fn_name)),
		};

		let output = $runtime::$fn_name($arg_name);
		$crate::runtime_api::Encode::encode(&output)
	};
	(@GENERATE_IMPL_CALL
		$runtime:ident;
		$fn_name:ident;
		$( $arg_name:ident : $arg_ty:ty ),*;
		$input:ident;
	) => {
		let ( $( $arg_name ),* ) : ($( $arg_ty ),*) = match $crate::runtime_api::Decode::decode(&mut $input) {
			Some(input) => input,
			None => panic!("Bad input data provided to {}", stringify!($fn_name)),
		};

		let output = $runtime::$fn_name($( $arg_name ),*);
		$crate::runtime_api::Encode::encode(&output)
	};
}
