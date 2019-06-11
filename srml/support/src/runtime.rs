// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Macros to define a runtime. A runtime is basically all your logic running in Substrate,
//! consisting of selected SRML modules and maybe some of your own modules.
//! A lot of supporting logic is automatically generated for a runtime,
//! mostly to combine data types and metadata of the included modules.

/// Construct a runtime, with the given name and the given modules.
///
/// The parameters here are specific types for `Block`, `NodeBlock`, and `InherentData`
/// and the modules that are used by the runtime.
/// `Block` is the block type that is used in the runtime and `NodeBlock` is the block type
/// that is used in the node. For instance they can differ in the extrinsics type.
///
/// # Example:
///
/// ```nocompile
/// construct_runtime!(
///     pub enum Runtime with Log(interalIdent: DigestItem<SessionKey>) where
///         Block = Block,
///         NodeBlock = runtime::Block,
///         UncheckedExtrinsic = UncheckedExtrinsic
///     {
///         System: system,
///         Test: test::{default, Log(Test)},
///         Test2: test_with_long_module::{Module},
///
///         // Module with instances
///         Test3_Instance1: test3::<Instance1>::{Module, Call, Storage, Event<T, I>, Config<T, I>, Origin<T, I>},
///         Test3_DefaultInstance: test3::{Module, Call, Storage, Event<T>, Config<T>, Origin<T>},
///     }
/// )
/// ```
///
/// The module `System: system` will expand to `System: system::{Module, Call, Storage, Event<T>, Config<T>}`.
/// The identifier `System` is the name of the module and the lower case identifier `system` is the
/// name of the Rust module/crate for this Substrate module.
///
/// The module `Test: test::{default, Log(Test)}` will expand to
/// `Test: test::{Module, Call, Storage, Event<T>, Config<T>, Log(Test)}`.
///
/// The module `Test2: test_with_long_module::{Module}` will expand to
/// `Test2: test_with_long_module::{Module}`.
///
/// We provide support for the following types in a module:
///
/// - `Module`
/// - `Call`
/// - `Storage`
/// - `Event` or `Event<T>` (if the event is generic) or `Event<T, I>` (if also over instance)
/// - `Origin` or `Origin<T>` (if the origin is generic) or `Origin<T, I>` (if also over instance)
/// - `Config` or `Config<T>` (if the config is generic) or `Config<T, I>` (if also over instance)
/// - `Log( $(IDENT),* )`
/// - `Inherent $( (CALL) )*` - If the module provides/can check inherents. The optional parameter
///                             is for modules that use a `Call` from a different module as
///                             inherent.
/// - `ValidateUnsigned`      - If the module validates unsigned extrinsics.
///
/// # Note
///
/// The population of the genesis storage depends on the order of modules. So, if one of your
/// modules depends on another module, the module that is depended upon needs to come before
/// the module depending on it.
#[macro_export]
macro_rules! construct_runtime {

	// Macro transformations (to convert invocations with incomplete parameters to the canonical
	// form)

	(
		pub enum $runtime:ident with Log ($log_internal:ident: DigestItem<$( $log_genarg:ty ),+>)
			where
				Block = $block:ident,
				NodeBlock = $node_block:ty,
				UncheckedExtrinsic = $uncheckedextrinsic:ident
		{
			$( $rest:tt )*
		}
	) => {
		$crate::construct_runtime!(
			{
				$runtime;
				$block;
				$node_block;
				$uncheckedextrinsic;
				$log_internal < $( $log_genarg ),* >;
			};
			{};
			$( $rest )*
		);
	};
	(
		{ $( $preset:tt )* };
		{ $( $expanded:tt )* };
		$name:ident: $module:ident,
		$( $rest:tt )*
	) => {
		$crate::construct_runtime!(
			{ $( $preset )* };
			{ $( $expanded )* $name: $module::{Module, Call, Storage, Event<T>, Config<T>}, };
			$( $rest )*
		);
	};
	(
		{ $( $preset:tt )* };
		{ $( $expanded:tt )* };
		$name:ident: $module:ident::{
			default,
			$(
				$modules:ident
					$( <$modules_generic:ident $(, $modules_instance:ident)?> )*
					$( ( $( $modules_args:ident ),* ) )*
			),*
		},
		$( $rest:tt )*
	) => {
		$crate::construct_runtime!(
			{ $( $preset )* };
			{
				$( $expanded )*
				$name: $module::{
					Module, Call, Storage, Event<T>, Config<T>,
					$(
						$modules $( <$modules_generic $(, $modules_instance)?> )*
						$( ( $( $modules_args ),* ) )*
					),*
				},
			};
			$( $rest )*
		);
	};
	(
		{ $( $preset:tt )* };
		{ $( $expanded:tt )* };
		$name:ident: $module:ident::{
			$(
				$modules:ident
					$( <$modules_generic:ident> )*
					$( ( $( $modules_args:ident ),* ) )*
			),*
		},
		$( $rest:tt )*
	) => {
		$crate::construct_runtime!(
			{ $( $preset )* };
			{
				$( $expanded )*
				$name: $module::{
					$(
						$modules $( <$modules_generic> )*
						$( ( $( $modules_args ),* ) )*
					),*
				},
			};
			$( $rest )*
		);
	};
	( // Instance module: we indicate the generic instance `I` with the full instance path
		{ $( $preset:tt )* };
		{ $( $expanded:tt )* };
		$name:ident: $module:ident ::< $module_instance:ident >::{
			$(
				$modules:ident
					$( <$modules_generic:ident $(, $modules_instance:ident )?> )*
					$( ( $( $modules_args:ident ),* ) )*
			),*
		},
		$( $rest:tt )*
	) => {
		$crate::construct_runtime!(
			{ $( $preset )* };
			{
				$( $expanded )*
				$name: $module::<$module_instance>::{
					$(
						$modules $( <$modules_generic $(, $modules_instance=$module::$module_instance)?> )*
						$( ( $( $modules_args ),* ) )*
					),*
				},
			};
			$( $rest )*
		);
	};

	// The main macro expansion that actually renders the Runtime code.

	(
		{
			$runtime:ident;
			$block:ident;
			$node_block:ty;
			$uncheckedextrinsic:ident;
			$log_internal:ident <$( $log_genarg:ty ),+>;
		};
		{
			$(
				$name:ident: $module:ident :: $( < $module_instance:ident >:: )? {
					$(
						$modules:ident
							$( <$modules_generic:ident $(, I=$modules_instance:path)?> )*
							$( ( $( $modules_args:ident ),* ) )*
					),*
				},
			)*
		};
	) => {
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		pub struct $runtime;
		impl $crate::runtime_primitives::traits::GetNodeBlockType for $runtime {
			type NodeBlock = $node_block;
		}
		impl $crate::runtime_primitives::traits::GetRuntimeBlockType for $runtime {
			type RuntimeBlock = $block;
		}
		$crate::__decl_instance_import!(
			$( $( $module < $module_instance > )? )*
		);
		$crate::__decl_outer_event!(
			$runtime;
			$(
				$name: $module:: $( < $module_instance >:: )? { $( $modules $( <$modules_generic $(, $modules_instance)?> )* ),* }
			),*
		);
		$crate::__decl_outer_origin!(
			$runtime;
			$(
				$name: $module:: $( < $module_instance >:: )? { $( $modules $( <$modules_generic $(, $modules_instance)?> )* ),* }
			),*
		);
		$crate::__decl_all_modules!(
			$runtime;
			;
			{};
			$(
				$name: $module:: $( < $module_instance >:: )? { $( $modules ),* },
			)*
		);
		$crate::__decl_outer_dispatch!(
			$runtime;
			;
			$(
				$name: $module::{ $( $modules ),* }
			),*;
		);
		$crate::__decl_runtime_metadata!(
			$runtime;
			{};
			$(
				$name: $module:: $( < $module_instance >:: )? { $( $modules )* }
			)*
		);
		$crate::__decl_outer_log!(
			$runtime;
			$log_internal < $( $log_genarg ),* >;
			{};
			$(
				$name: $module:: $( < $module_instance >:: )? { $( $modules $( ( $( $modules_args )* ) )* )* }
			)*
		);
		$crate::__decl_outer_config!(
			$runtime;
			{};
			$(
				$name: $module:: $( < $module_instance >:: )? {
					$( $modules $( <$modules_generic $(, $modules_instance)?> )* ),*
				},
			)*
		);
		$crate::__decl_outer_inherent!(
			$runtime;
			$block;
			$uncheckedextrinsic;
			;
			$(
				$name: $module::{ $( $modules $( ( $( $modules_args )* ) )* ),* }
			),*;
		);
		$crate::__impl_outer_validate_unsigned!(
			$runtime;
			{};
			$(
				$name: $module::{ $( $modules $( ( $( $modules_args )* ) )* )* }
			)*
		);
	}
}

/// A macro that generates a "__decl" private macro that transforms parts of the runtime definition
/// to feed them into a public "impl" macro which accepts the format
/// "pub enum $name for $runtime where system = $system".
///
/// Used to define Event and Origin associated types.
#[macro_export]
#[doc(hidden)]
macro_rules! __create_decl_macro {
	(
		// Parameter $d is a hack for the following issue:
		// https://github.com/rust-lang/rust/issues/35853
		$macro_name:ident, $macro_outer_name:ident, $macro_enum_name:ident, $d:tt
	) => {
		#[macro_export]
		#[doc(hidden)]
		macro_rules! $macro_name {
			(
				$runtime:ident;
				$d( $name:ident : $module:ident:: $d( < $module_instance:ident >:: )? {
					$d( $modules:ident $d( <$modules_generic:ident $d(, $modules_instance:path)?> ),* ),*
				}),*
			) => {
				$d crate::$macro_name!(@inner
					$runtime;
					;
					{};
					$d(
						$name: $module:: $d( < $module_instance >:: )? {
							$d( $modules $d( <$modules_generic $d(, $modules_instance)?> )* ),*
						},
					)*
				);
			};
			(@inner
				$runtime:ident;
				; // there can not be multiple `System`s
				{ $d( $parsed:tt )* };
				System: $module:ident::{
					$d( $modules:ident $d( <$modules_generic:ident> )* ),*
				},
				$d( $rest:tt )*
			) => {
				$d crate::$macro_name!(@inner
					$runtime;
					$module;
					{ $d( $parsed )* };
					$d( $rest )*
				);
			};
			(@inner
				$runtime:ident;
				$d( $system:ident )?;
				{ $d( $parsed:tt )* };
				$name:ident : $module:ident:: < $module_instance:ident >:: {
					$macro_enum_name <$event_generic:ident, $event_instance:path> $d(, $ignore:ident $d( <$ignor:ident $d(, $ignore_instance:path)?> )* )*
				},
				$d( $rest:tt )*
			) => {
				$d crate::$macro_name!(@inner
					$runtime;
					$d( $system )?;
					{
						$d( $parsed )*
						$module $module_instance <$event_generic, $event_instance>,
					};
					$d( $rest )*
				);
			};
			(@inner
				$runtime:ident;
				$d( $system:ident )?;
				{ $d( $parsed:tt )* };
				$name:ident : $module:ident:: < $module_instance:ident >:: {
					$macro_enum_name $d( <$event_generic:ident> )* $d(, $ignore:ident $d( <$ignor:ident $d(, $ignore_instance:path)?> )* )*
				},
				$d( $rest:tt )*
			) => {
				compile_error!{concat!{
					"Module `", stringify!{$name}, "` must have `", stringify!{$macro_enum_name}, "<T, I>`",
					" but has `", stringify!{$macro_enum_name} $d(, "<", stringify!{$event_generic}, ">")*, "`",
					": Instantiated modules must have ", stringify!{$macro_enum_name},
					" generic over instance to be able to convert to outer ", stringify!{$macro_enum_name}
				}}
			};
			(@inner
				$runtime:ident;
				$d( $system:ident )?;
				{ $d( $parsed:tt )* };
				$name:ident : $module:ident:: {
					$macro_enum_name $d( <$event_generic:ident $d(, $event_instance:path)?> )* $d(, $ignore:ident $d( <$ignor:ident $d(, $ignore_instance:path)?> )* )*
				},
				$d( $rest:tt )*
			) => {
				$d crate::$macro_name!(@inner
					$runtime;
					$d( $system )?;
					{
						$d( $parsed )*
						$module $d( <$event_generic $d(, $event_instance)?> )*,
					};
					$d( $rest )*
				);
			};
			(@inner
				$runtime:ident;
				$d( $system:ident )?;
				{ $d( $parsed:tt )* };
				$name:ident : $module:ident:: $d( < $module_instance:ident >:: )? {
					$ignore:ident $d( <$ignor:ident $d(, $ignore_instance:path)?> )* $d(, $modules:ident $d( <$modules_generic:ident $d(, $modules_instance:path)?> )* )*
				},
				$d( $rest:tt )*
			) => {
				$d crate::$macro_name!(@inner
					$runtime;
					$d( $system )?;
					{ $d( $parsed )* };
					$name: $module:: $d( < $module_instance >:: )? { $d( $modules $d( <$modules_generic $d(, $modules_instance)?> )* ),* },
					$d( $rest )*
				);
			};
			(@inner
				$runtime:ident;
				$d( $system:ident )?;
				{ $d( $parsed:tt )* };
				$name:ident: $module:ident:: $d( < $module_instance:ident >:: )? {},
				$d( $rest:tt )*
			) => {
				$d crate::$macro_name!(@inner
					$runtime;
					$d( $system )?;
					{ $d( $parsed )* };
					$d( $rest )*
				);
			};
			(@inner
				$runtime:ident;
				$system:ident;
				{ $d( $parsed_modules:ident $d( $instance:ident )? $d( <$parsed_generic:ident $d(, $parsed_instance_full_path:path)?> )* ,)* };
			) => {
				$d crate::paste::item! {
					$d crate::$macro_outer_name! {

						pub enum $macro_enum_name for $runtime where system = $system {
							$d(
								[< $parsed_modules $d(_ $instance )? >] $d( <$parsed_generic $d(, $parsed_instance_full_path)?> )*,
							)*
						}
					}
				}
			}
		}
	}
}

__create_decl_macro!(__decl_outer_event, impl_outer_event, Event, $);
__create_decl_macro!(__decl_outer_origin, impl_outer_origin, Origin, $);

/// A macro that defines all modules as an associated types of the Runtime type.
#[macro_export]
#[doc(hidden)]
macro_rules! __decl_all_modules {
	(
		$runtime:ident;
		;
		{ $( $parsed:tt )* };
		System: $module:ident::{ Module $(, $modules:ident )* },
		$( $rest:tt )*
	) => {
		$crate::__decl_all_modules!(
			$runtime;
			$module;
			{ $( $parsed )* };
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		$( $system:ident )?;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $( < $module_instance:ident >:: )? { Module $(, $modules:ident )* },
		$( $rest:tt )*
	) => {
		$crate::__decl_all_modules!(
			$runtime;
			$( $system )?;
			{
				$( $parsed )*
				$module::$name $(<$module_instance>)?,
			};
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		$( $system:ident )?;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $( < $module_instance:ident >:: )? { $ignore:ident $(, $modules:ident )* },
		$( $rest:tt )*
	) => {
		$crate::__decl_all_modules!(
			$runtime;
			$( $system )?;
			{ $( $parsed )* };
			$name: $module::{ $( $modules ),* },
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		$( $system:ident )?;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $( < $module_instance:ident >:: )? {},
		$( $rest:tt )*
	) => {
		$crate::__decl_all_modules!(
			$runtime;
			$( $system )?;
			{ $( $parsed )* };
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		$system:ident;
		{ $( $parsed_module:ident :: $parsed_name:ident $(<$instance:ident>)? ,)*};
	) => {
		pub type System = system::Module<$runtime>;
		$(
			pub type $parsed_name = $parsed_module::Module<$runtime $(, $parsed_module::$instance )?>;
		)*
		type AllModules = ( $( $parsed_name, )* );
	}
}

/// A macro that defines the Call enum to represent calls to functions in the modules included
/// in the runtime (by wrapping the values of all FooModule::Call enums).
#[macro_export]
#[doc(hidden)]
macro_rules! __decl_outer_dispatch {
	(
		$runtime:ident;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		System: $module:ident::{
			$ignore:ident $( <$ignor:ident> )* $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_outer_dispatch!(
			$runtime;
			$( $parsed_modules :: $parsed_name ),*;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( <$rest_modules_generic> )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		$name:ident: $module:ident::{
			Call $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_outer_dispatch!(
			$runtime;
			$( $parsed_modules :: $parsed_name, )* $module::$name;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( <$rest_modules_generic> )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		$name:ident: $module:ident::{
			$ignore:ident $( <$ignor:ident> )* $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_outer_dispatch!(
			$runtime;
			$( $parsed_modules :: $parsed_name ),*;
			$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			$(
				, $rest_name: $rest_module::{
					$( $rest_modules $( <$rest_modules_generic> )* ),*
				}
			)*;
		);
	};
	(
		$runtime:ident;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		$name:ident: $module:ident::{}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_outer_dispatch!(
			$runtime;
			$( $parsed_modules :: $parsed_name ),*;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( <$rest_modules_generic> )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		;
	) => {
		$crate::impl_outer_dispatch!(
			pub enum Call for $runtime where origin: Origin {
				$( $parsed_modules::$parsed_name, )*
			}
		);
	};
}

/// A private macro that generates metadata() method for the runtime. See impl_runtime_metadata macro.
#[macro_export]
#[doc(hidden)]
macro_rules! __decl_runtime_metadata {
	// leading is Module : parse
	(
		$runtime:ident;
		{ $( $parsed:tt )* };
		$( { leading_module: $( $leading_module:ident )* } )?
		$name:ident: $module:ident:: $( < $module_instance:ident >:: )? {
			Module $( $modules:ident )*
		}
		$( $rest:tt )*
	) => {
		$crate::__decl_runtime_metadata!(
			$runtime;
			{
				$( $parsed )*
				$module $( < $module_instance > )?  { $( $( $leading_module )* )? $( $modules )* }
			};
			$( $rest )*
		);
	};
	// leading isn't Module : put it in leadings
	(
		$runtime:ident;
		{ $( $parsed:tt )* };
		$( { leading_module: $( $leading_module:ident )* } )?
		$name:ident: $module:ident:: $( < $module_instance:ident >:: )? {
			$other_module:ident $( $modules:ident )*
		}
		$( $rest:tt )*
	) => {
		$crate::__decl_runtime_metadata!(
			$runtime;
			{ $( $parsed )* };
			{ leading_module: $( $( $leading_module )* )? $other_module }
			$name: $module:: $( < $module_instance >:: )? {
				$( $modules )*
			}
			$( $rest )*
		);
	};
	// does not contain Module : skip
	(
		$runtime:ident;
		{ $( $parsed:tt )* };
		$( { leading_module: $( $leading_module:ident )* } )?
		$name:ident: $module:ident:: $( < $module_instance:ident >:: )? {}
		$( $rest:tt )*
	) => {
		$crate::__decl_runtime_metadata!(
			$runtime;
			{ $( $parsed )* };
			$( $rest )*
		);
	};
	// end of decl
	(
		$runtime:ident;
		{ $( $parsed_modules:ident $( < $module_instance:ident > )? { $( $withs:ident )* } )* };
	) => {
		$crate::impl_runtime_metadata!(
			for $runtime with modules
				$( $parsed_modules::Module $( < $module_instance > )? with $( $withs )* , )*
		);
	}

}
/// A private macro that generates Log enum for the runtime. See impl_outer_log macro.
#[macro_export]
#[doc(hidden)]
macro_rules! __decl_outer_log {
	(
		$runtime:ident;
		$log_internal:ident <$( $log_genarg:ty ),+>;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $(<$module_instance:ident>::)? {
			Log ( $( $args:ident )* ) $( $modules:ident $( ( $( $modules_args:ident )* ) )* )*
		}
		$( $rest:tt )*
	) => {
		$crate::__decl_outer_log!(
			$runtime;
			$log_internal < $( $log_genarg ),* >;
			{ $( $parsed )* $module $(<$module_instance>)? ( $( $args )* )};
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		$log_internal:ident <$( $log_genarg:ty ),+>;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $(<$module_instance:ident>::)? {
			$ignore:ident $( ( $( $args_ignore:ident )* ) )*
			$( $modules:ident $( ( $( $modules_args:ident )* ) )* )*
		}
		$( $rest:tt )*
	) => {
		$crate::__decl_outer_log!(
			$runtime;
			$log_internal < $( $log_genarg ),* >;
			{ $( $parsed )* };
			$name: $module:: $(<$module_instance>::)? { $( $modules $( ( $( $modules_args )* ) )* )* }
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		$log_internal:ident <$( $log_genarg:ty ),+>;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $(<$module_instance:ident>::)? {}
		$( $rest:tt )*
	) => {
		$crate::__decl_outer_log!(
			$runtime;
			$log_internal < $( $log_genarg ),* >;
			{ $( $parsed )* };
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		$log_internal:ident <$( $log_genarg:ty ),+>;
		{ $(
			$parsed_modules:ident $(< $parsed_instance:ident >)? ( $( $parsed_args:ident )* )
		)* };
	) => {
		$crate::paste::item! {
			$crate::runtime_primitives::impl_outer_log!(
				pub enum Log($log_internal: DigestItem<$( $log_genarg ),*>) for $runtime {
					$( [< $parsed_modules $(_ $parsed_instance)? >] $(< $parsed_modules::$parsed_instance >)? ( $( $parsed_args ),* ) ),*
				}
			);
		}
	};
}

/// A private macro that generates GenesisConfig for the runtime. See impl_outer_config macro.
#[macro_export]
#[doc(hidden)]
macro_rules! __decl_outer_config {
	(
		$runtime:ident;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $( < $module_instance:ident >:: )? {
			Config $(< $config_generic:ident $(, $config_instance:path)?>)? $(, $modules:ident $( <$modules_generic:ident $(, $modules_instance:path)?> )* )*
		},
		$( $rest:tt )*
	) => {
		$crate::__decl_outer_config!(
			$runtime;
			{
				$( $parsed )*
				$module::$name $( $module_instance )?  $(<$config_generic $(, $config_instance)?>)?,
			};
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $( < $module_instance:ident >:: )? {
			$ignore:ident $( <$ignor:ident $(, $ignore_instance:path)?> )* $(, $modules:ident $( <$modules_generic:ident $(, $modules_instance:path)?> )* )*
		},
		$( $rest:tt )*
	) => {
		$crate::__decl_outer_config!(
			$runtime;
			{ $( $parsed )* };
			$name: $module:: $( < $module_instance >:: )? { $( $modules $( <$modules_generic $(, $modules_instance)?> )* ),* },
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $( < $module_instance:ident >:: )? {},
		$( $rest:tt )*
	) => {
		$crate::__decl_outer_config!(
			$runtime;
			{ $( $parsed )* };
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		{$( $parsed_modules:ident :: $parsed_name:ident $( $parsed_instance:ident )?  $( < $parsed_generic:ident $(, $parsed_instance_full_path:path)? > )* ,)* };
	) => {
		$crate::paste::item! {
			$crate::runtime_primitives::impl_outer_config!(
				pub struct GenesisConfig for $runtime {
					$(
						[< $parsed_name Config >] => [< $parsed_modules $( _ $parsed_instance)? >] $( < $parsed_generic $(, $parsed_instance_full_path)? > )*,
					)*
				}
			);
		}
	};
}

/// A private macro that generates check_inherents() implementation for the runtime.
#[macro_export]
#[doc(hidden)]
macro_rules! __decl_outer_inherent {
	(
		$runtime:ident;
		$block:ident;
		$uncheckedextrinsic:ident;
		$( $parsed_name:ident :: $parsed_call:ident ),*;
		$name:ident: $module:ident::{
			Inherent $(, $modules:ident $( ( $( $modules_call:ident )* ) )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( ( $( $rest_call:ident )* ) )* ),*
		})*;
	) => {
		$crate::__decl_outer_inherent!(
			$runtime;
			$block;
			$uncheckedextrinsic;
			$( $parsed_name :: $parsed_call, )* $name::$name;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( ( $( $rest_call )* ) )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$block:ident;
		$uncheckedextrinsic:ident;
		$( $parsed_name:ident :: $parsed_call:ident ),*;
		$name:ident: $module:ident::{
			Inherent ( $call:ident ) $(, $modules:ident $( ( $( $modules_call:ident )* ) )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( ( $( $rest_call:ident )* ) )* ),*
		})*;
	) => {
		$crate::__decl_outer_inherent!(
			$runtime;
			$block;
			$uncheckedextrinsic;
			$( $parsed_name :: $parsed_call, )* $name::$call;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( ( $( $rest_call )* ) )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$block:ident;
		$uncheckedextrinsic:ident;
		$( $parsed_name:ident :: $parsed_call:ident ),*;
		$name:ident: $module:ident::{
			$ignore:ident $( ( $( $ignor:ident )* ) )*
				$(, $modules:ident $( ( $( $modules_call:ident )* ) )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( ( $( $rest_call:ident )* ) )* ),*
		})*;
	) => {
		$crate::__decl_outer_inherent!(
			$runtime;
			$block;
			$uncheckedextrinsic;
			$( $parsed_name :: $parsed_call ),*;
			$name: $module::{ $( $modules $( ( $( $modules_call )* ) )* ),* }
			$(
				, $rest_name: $rest_module::{
					$( $rest_modules $( ( $( $rest_call )* ) )* ),*
				}
			)*;
		);
	};
	(
		$runtime:ident;
		$block:ident;
		$uncheckedextrinsic:ident;
		$( $parsed_name:ident :: $parsed_call:ident ),*;
		$name:ident: $module:ident::{}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( ( $( $rest_call:ident )* ) )* ),*
		})*;
	) => {
		$crate::__decl_outer_inherent!(
			$runtime;
			$block;
			$uncheckedextrinsic;
			$( $parsed_name :: $parsed_call ),*;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( ( $( $rest_call )* ) )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$block:ident;
		$uncheckedextrinsic:ident;
		$( $parsed_name:ident :: $parsed_call:ident ),*;
		;
	) => {
		$crate::impl_outer_inherent!(
			impl Inherents where Block = $block, UncheckedExtrinsic = $uncheckedextrinsic {
				$( $parsed_name : $parsed_call, )*
			}
		);
	};
}

#[macro_export]
#[doc(hidden)]
// Those imports are used by event, config, origin and log macros to get access to its inner type
macro_rules! __decl_instance_import {
	( $( $module:ident <$instance:ident> )* ) => {
		$crate::paste::item! {
			$(use $module as [< $module _ $instance >];)*
		}
	};
}

/// A private macro that calls impl_outer_validate_unsigned for Call.
#[macro_export]
#[doc(hidden)]
macro_rules! __impl_outer_validate_unsigned {
	(
		$runtime:ident;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $(<$module_instance:ident>::)? {
			ValidateUnsigned $( $modules:ident $( ( $( $modules_args:ident )* ) )* )*
		}
		$( $rest:tt )*
	) => {
		$crate::__impl_outer_validate_unsigned!(
			$runtime;
			{ $( $parsed )* $name };
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $(<$module_instance:ident>::)? {
			$ignore:ident $( ( $( $args_ignore:ident )* ) )*
			$( $modules:ident $( ( $( $modules_args:ident )* ) )* )*
		}
		$( $rest:tt )*
	) => {
		$crate::__impl_outer_validate_unsigned!(
			$runtime;
			{ $( $parsed )* };
			$name: $module:: $(<$module_instance>::)? {
				$( $modules $( ( $( $modules_args )* ) )* )*
			}
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		{ $( $parsed:tt )* };
		$name:ident: $module:ident:: $(<$module_instance:ident>::)? {}
		$( $rest:tt )*
	) => {
		$crate::__impl_outer_validate_unsigned!(
			$runtime;
			{ $( $parsed )* };
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		{ $(
			$parsed_modules:ident
		)* };
	) => {
		$crate::impl_outer_validate_unsigned!(
			impl ValidateUnsigned for $runtime {
				$( $parsed_modules )*
			}
		);
	};
}
