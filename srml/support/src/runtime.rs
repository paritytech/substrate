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
//! mostly for to combine data types and metadata of the included modules.

/// Construct a runtime, with the given name and the given modules.
///
/// The parameters here are specific types for Block, NodeBlock and InherentData
/// (TODO: describe the difference between Block and NodeBlock)
///	and the modules that are used by the runtime.
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
/// - `Module`
/// - `Call`
/// - `Storage`
/// - `Event` or `Event<T>` (if the event is generic)
/// - `Origin` or `Origin<T>` (if the origin is generic)
/// - `Config` or `Config<T>` (if the config is generic)
/// - `Log( $(IDENT),* )`
/// - `Inherent $( (CALL) )*` - If the module provides/can check inherents. The optional parameter
///                             is for modules that use a `Call` from a different module as
///                             inherent.
///
/// # Note
///
/// The population of the genesis storage depends on the order of modules. So, if one of your
/// modules depends on another module. The dependent module need to come before the module depending on it.
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
		construct_runtime!(
			$runtime;
			$block;
			$node_block;
			$uncheckedextrinsic;
			$log_internal < $( $log_genarg ),* >;
			;
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		$block:ident;
		$node_block:ty;
		$uncheckedextrinsic:ident;
		$log_internal:ident <$( $log_genarg:ty ),+>;
		$(
			$expanded_name:ident: $expanded_module:ident::{
				$(
					$expanded_modules:ident
						$( <$expanded_modules_generic:ident> )*
						$( ( $( $expanded_modules_args:ident ),* ) )*
				),*
			}
		),*;
		$name:ident: $module:ident,
		$(
			$rest_name:ident: $rest_module:ident $(
				::{
					$(
						$rest_modules:ident
							$( <$rest_modules_generic:ident> )*
							$( ( $( $rest_modules_args:ident ),* ) )*
					),*
				}
			)*,
		)*
	) => {
		construct_runtime!(
			$runtime;
			$block;
			$node_block;
			$uncheckedextrinsic;
			$log_internal < $( $log_genarg ),* >;
			$(
				$expanded_name: $expanded_module::{
					$(
						$expanded_modules
							$( <$expanded_modules_generic> )*
							$( ( $( $expanded_modules_args ),* ) )*
					),*
				},
			)* $name: $module::{Module, Call, Storage, Event<T>, Config<T>};
			$(
				$rest_name: $rest_module $(
					::{
						$(
							$rest_modules
								$( <$rest_modules_generic> )*
								$( ( $( $rest_modules_args ),* ) )*
						),*
					}
				)*,
			)*
		);
	};
	(
		$runtime:ident;
		$block:ident;
		$node_block:ty;
		$uncheckedextrinsic:ident;
		$log_internal:ident <$( $log_genarg:ty ),+>;
		$(
			$expanded_name:ident: $expanded_module:ident::{
				$(
					$expanded_modules:ident
						$( <$expanded_modules_generic:ident> )*
						$( ( $( $expanded_modules_args:ident ),* ) )*
				),*
			}
		),*;
		$name:ident: $module:ident::{
			default,
			$(
				$modules:ident
					$( <$modules_generic:ident> )*
					$( ( $( $modules_args:ident ),* ) )*
			),*
		},
		$(
			$rest_name:ident: $rest_module:ident $(
				::{
					$(
						$rest_modules:ident
							$( <$rest_modules_generic:ident> )*
							$( ( $( $rest_modules_args:ident ),* ) )*
					),*
				}
			)*,
		)*
	) => {
		construct_runtime!(
			$runtime;
			$block;
			$node_block;
			$uncheckedextrinsic;
			$log_internal < $( $log_genarg ),* >;
			$(
				$expanded_name: $expanded_module::{
					$(
						$expanded_modules
							$( <$expanded_modules_generic> )*
							$( ( $( $expanded_modules_args ),* ) )*
					),*
				},
			)*
			$name: $module::{
				Module, Call, Storage, Event<T>, Config<T>,
				$(
					$modules $( <$modules_generic> )* $( ( $( $modules_args ),* ) )*
				),*
			};
			$(
				$rest_name: $rest_module $(
					::{
						$(
							$rest_modules
								$( <$rest_modules_generic> )*
								$( ( $( $rest_modules_args ),* ) )*
						),*
					}
				)*,
			)*
		);
	};
	(
		$runtime:ident;
		$block:ident;
		$node_block:ty;
		$uncheckedextrinsic:ident;
		$log_internal:ident <$( $log_genarg:ty ),+>;
		$(
			$expanded_name:ident: $expanded_module:ident::{
				$(
					$expanded_modules:ident
						$( <$expanded_modules_generic:ident> )*
						$( ( $( $expanded_modules_args:ident ),* ) )*
				),*
			}
		),*;
		$name:ident: $module:ident::{
			$(
				$modules:ident
					$( <$modules_generic:ident> )*
					$( ( $( $modules_args:ident ),* ) )*
			),*
		},
		$(
			$rest_name:ident: $rest_module:ident $(
				::{
					$(
						$rest_modules:ident
							$( <$rest_modules_generic:ident> )*
							$( ( $( $rest_modules_args:ident ),* ) )*
					),*
				}
			)*,
		)*
	) => {
		construct_runtime!(
			$runtime;
			$block;
			$node_block;
			$uncheckedextrinsic;
			$log_internal < $( $log_genarg ),* >;
			$(
				$expanded_name: $expanded_module::{
					$(
						$expanded_modules
							$( <$expanded_modules_generic> )*
							$( ( $( $expanded_modules_args ),* ) )*
					),*
				},
			)*
			$name: $module::{
				$(
					$modules $( <$modules_generic> )* $( ( $( $modules_args ),* ) )*
				),*
			};
			$(
				$rest_name: $rest_module $(
					::{
						$(
							$rest_modules
								$( <$rest_modules_generic> )*
								$( ( $( $rest_modules_args ),* ) )*
						),*
					}
				)*,
			)*
		);
	};

	// The main macro expansion that actually renders the Runtime code.

	(
		$runtime:ident;
		$block:ident;
		$node_block:ty;
		$uncheckedextrinsic:ident;
		$log_internal:ident <$( $log_genarg:ty ),+>;
		$(
			$name:ident: $module:ident::{
				$(
					$modules:ident
						$( <$modules_generic:ident> )*
						$( ( $( $modules_args:ident ),* ) )*
				),*
			}
		),*;
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
		$crate::__decl_outer_event!(
			$runtime;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*
		);
		$crate::__decl_outer_origin!(
			$runtime;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*
		);
		$crate::__decl_all_modules!(
			$runtime;
			;
			;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*;
		);
		$crate::__decl_outer_dispatch!(
			$runtime;
			;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*;
		);
		$crate::__decl_runtime_metadata!(
			$runtime;
			;
			$(
				$name: $module::{ $( $modules )* }
			)*
		);
		$crate::__decl_outer_log!(
			$runtime;
			$log_internal < $( $log_genarg ),* >;
			;
			$(
				$name: $module::{ $( $modules $( ( $( $modules_args ),* ) )* ),* }
			),*;
		);
		$crate::__decl_outer_config!(
			$runtime;
			;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*;
		);
		$crate::__decl_outer_inherent!(
			$runtime;
			$block;
			$uncheckedextrinsic;
			;
			$(
				$name: $module::{ $( $modules $( ( $( $modules_args ),* ) )* ),* }
			),*;
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
				$d( $name:ident : $module:ident::{
					$d( $modules:ident $d( <$modules_generic:ident> )* ),*
				}),*
			) => {
				$d crate::$macro_name!(@inner
					$runtime;
					;
					;
					$d(
						$name: $module::{
							$d( $modules $d( <$modules_generic> )* ),*
						}
					),*;
				);
			};
			(@inner
				$runtime:ident;
				; // there can not be multiple `System`s
				$d( $parsed_modules:ident $d( <$parsed_generic:ident> )* ),*;
				System: $module:ident::{
					$ingore:ident $d( <$ignor:ident> )* $d(, $modules:ident $d( <$modules_generic:ident> )* )*
				}
				$d(, $rest_name:ident : $rest_module:ident::{
					$d( $rest_modules:ident $d( <$rest_modules_generic:ident> )* ),*
				})*;
			) => {
				$d crate::$macro_name!(@inner
					$runtime;
					$module;
					$d( $parsed_modules $d( <$parsed_generic> )* ),*;
					$d(
						$rest_name: $rest_module::{
							$d( $rest_modules $d( <$rest_modules_generic> )* ),*
						}
					),*;
				);
			};
			(@inner
				$runtime:ident;
				$d( $system:ident )*;
				$d( $parsed_modules:ident $d( <$parsed_generic:ident> )* ),*;
				$name:ident: $module:ident::{
					$macro_enum_name $d( <$event_gen:ident> )* $d(, $modules:ident $d( <$modules_generic:ident> )* )*
				}
				$d(, $rest_name:ident : $rest_module:ident::{
					$d( $rest_modules:ident $d( <$rest_modules_generic:ident> )* ),*
				})*;
			) => {
				$d crate::$macro_name!(@inner
					$runtime;
					$d( $system )*;
					$d(
						$parsed_modules $d( <$parsed_generic> )* , )*
						$module $d( <$event_gen> )*;
					$d(
						$rest_name: $rest_module::{
							$d( $rest_modules $d( <$rest_modules_generic> )* ),*
						}
					),*;
				);
			};
			(@inner
				$runtime:ident;
				$d( $system:ident )*;
				$d( $parsed_modules:ident $d( <$parsed_generic:ident> )* ),*;
				$name:ident: $module:ident::{
					$ingore:ident $d( <$ignor:ident> )* $d(, $modules:ident $d( <$modules_generic:ident> )* )*
				}
				$d(, $rest_name:ident : $rest_module:ident::{
					$d( $rest_modules:ident $d( <$rest_modules_generic:ident> )* ),*
				})*;
			) => {
				$d crate::$macro_name!(@inner
					$runtime;
					$d( $system )*;
					$d( $parsed_modules $d( <$parsed_generic> )* ),*;
					$name: $module::{ $d( $modules $d( <$modules_generic> )* ),* }
					$d(
						, $rest_name: $rest_module::{
							$d( $rest_modules $d( <$rest_modules_generic> )* ),*
						}
					)*;
				);
			};
			(@inner
				$runtime:ident;
				$d( $system:ident )*;
				$d( $parsed_modules:ident $d( <$parsed_generic:ident> )* ),*;
				$name:ident: $module:ident::{}
				$d(, $rest_name:ident : $rest_module:ident::{
					$d( $rest_modules:ident $d( <$rest_modules_generic:ident> )* ),*
				})*;
			) => {
				$d crate::$macro_name!(@inner
					$runtime;
					$d( $system )*;
					$d( $parsed_modules $d( <$parsed_generic> )* ),*;
					$d(
						$rest_name: $rest_module::{
							$d( $rest_modules $d( <$rest_modules_generic> )* ),*
						}
					),*;
				);
			};
			(@inner
				$runtime:ident;
				$d( $system:ident )+;
				$d( $parsed_modules:ident $d( <$parsed_generic:ident> )* ),*;
				;
			) => {
				$d crate::$macro_outer_name! {
					pub enum $macro_enum_name for $runtime where system = $d( $system )* {
						$d(
							$parsed_modules $d( <$parsed_generic> )*,
						)*
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
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		System: $module:ident::{
			Module $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_all_modules!(
			$runtime;
			$module;
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
		$( $system:ident )*;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		$name:ident: $module:ident::{
			Module $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_all_modules!(
			$runtime;
			$( $system )*;
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
		$( $system:ident )*;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		$name:ident: $module:ident::{
			$ingore:ident $( <$ignor:ident> )* $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_all_modules!(
			$runtime;
			$( $system )*;
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
		$( $system:ident )*;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		$name:ident: $module:ident::{}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_all_modules!(
			$runtime;
			$( $system )*;
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
		$system:ident;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		;
	) => {
		pub type System = system::Module<$runtime>;
		$(
			pub type $parsed_name = $parsed_modules::Module<$runtime>;
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
			$ingore:ident $( <$ignor:ident> )* $(, $modules:ident $( <$modules_generic:ident> )* )*
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
			$ingore:ident $( <$ignor:ident> )* $(, $modules:ident $( <$modules_generic:ident> )* )*
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
		$( $parsed_modules:ident { $( $withs:ident )* } )*;
		$( { leading_module: $( $leading_module:ident )* } )?
		$name:ident: $module:ident::{
			Module $( $modules:ident )*
		}
		$( $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident )*
		})*
	) => {
		$crate::__decl_runtime_metadata!(
			$runtime;
			$( $parsed_modules { $( $withs )* } )* $module { $( $( $leading_module )* )? $( $modules )* };
			$(
				$rest_name: $rest_module::{
					$( $rest_modules )*
				}
			)*
		);
	};
	// leading isn't Module : put it in leadings
	(
		$runtime:ident;
		$( $parsed_modules:ident { $( $withs:ident )* } )*;
		$( { leading_module: $( $leading_module:ident )* } )?
		$name:ident: $module:ident::{
			$other_module:ident $( $modules:ident )*
		}
		$( $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident )*
		})*
	) => {
		$crate::__decl_runtime_metadata!(
			$runtime;
			$( $parsed_modules { $( $withs )* } )*;
			{ leading_module: $( $( $leading_module )* )? $other_module }
			$name: $module::{
				$( $modules )*
			}
			$(
				$rest_name: $rest_module::{
					$( $rest_modules )*
				}
			)*
		);
	};
	// does not contain Module : skip
	(
		$runtime:ident;
		$( $parsed_modules:ident { $( $withs:ident )* } )*;
		$( { leading_module: $( $leading_module:ident )* } )?
		$name:ident: $module:ident::{}
		$( $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident )*
		})*
	) => {
		$crate::__decl_runtime_metadata!(
			$runtime;
			$( $parsed_modules { $( $withs )* } )*;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules )*
				}
			)*
		);
	};
	// end of decl
	(
		$runtime:ident;
		$( $parsed_modules:ident { $( $withs:ident )* } )*;
	) => {
		$crate::impl_runtime_metadata!(
			for $runtime with modules
				$( $parsed_modules::Module with $( $withs )* , )*
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
		$( $parsed_modules:ident( $( $parsed_args:ident ),* ) ),*;
		$name:ident: $module:ident::{
			Log ( $( $args:ident ),* ) $(, $modules:ident $( ( $( $modules_args:ident )* ) )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( ( $( $rest_modules_args:ident )* ) )* ),*
		})*;
	) => {
		$crate::__decl_outer_log!(
			$runtime;
			$log_internal < $( $log_genarg ),* >;
			$( $parsed_modules ( $( $parsed_args ),* ), )* $module ( $( $args ),* );
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( ( $( $rest_modules_args ),* ) )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$log_internal:ident <$( $log_genarg:ty ),+>;
		$( $parsed_modules:ident( $( $parsed_args:ident ),* ) ),*;
		$name:ident: $module:ident::{
			$ignore:ident $( ( $( $args_ignore:ident ),* ) )*
			$(, $modules:ident $( ( $( $modules_args:ident ),* ) )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
				$( $rest_modules:ident $( ( $( $rest_modules_args:ident )* ) )* ),*
		})*;
	) => {
		$crate::__decl_outer_log!(
			$runtime;
			$log_internal < $( $log_genarg ),* >;
			$( $parsed_modules ( $( $parsed_args ),* ) ),*;
			$name: $module::{ $( $modules $( ( $( $modules_args ),* ) )* ),* }
			$(
				, $rest_name: $rest_module::{
					$( $rest_modules $( ( $( $rest_modules_args ),* ) )* ),*
				}
			)*;
		);
	};
	(
		$runtime:ident;
		$log_internal:ident <$( $log_genarg:ty ),+>;
		$( $parsed_modules:ident( $( $parsed_args:ident ),* ) ),*;
		$name:ident: $module:ident::{}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( ( $( $rest_modules_args:ident )* ) )* ),*
		})*;
	) => {
		$crate::__decl_outer_log!(
			$runtime;
			$log_internal < $( $log_genarg ),* >;
			$( $parsed_modules ( $( $parsed_args ),* ) ),*;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( ( $( $rest_modules_args ),* ) )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$log_internal:ident <$( $log_genarg:ty ),+>;
		$( $parsed_modules:ident( $( $parsed_args:ident ),* ) ),*;
		;
	) => {
		$crate::runtime_primitives::impl_outer_log!(
			pub enum Log($log_internal: DigestItem<$( $log_genarg ),*>) for $runtime {
				$( $parsed_modules ( $( $parsed_args ),* ) ),*
			}
		);
	};
}

/// A private macro that generates GenesisConfig for the runtime. See impl_outer_config macro.
#[macro_export]
#[doc(hidden)]
macro_rules! __decl_outer_config {
	(
		$runtime:ident;
		$( $parsed_modules:ident :: $parsed_name:ident $( < $parsed_generic:ident > )* ),*;
		$name:ident: $module:ident::{
			Config $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_outer_config!(
			$runtime;
			$( $parsed_modules :: $parsed_name $( < $parsed_generic > )*, )* $module::$name;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( <$rest_modules_generic> )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$( $parsed_modules:ident :: $parsed_name:ident $( < $parsed_generic:ident > )* ),*;
		$name:ident: $module:ident::{
			Config<T> $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_outer_config!(
			$runtime;
			$( $parsed_modules :: $parsed_name $( < $parsed_generic > )*, )* $module::$name<T>;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( <$rest_modules_generic> )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$( $parsed_modules:ident :: $parsed_name:ident $( < $parsed_generic:ident > )* ),*;
		$name:ident: $module:ident::{
			$ingore:ident $( <$ignor:ident> )* $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_outer_config!(
			$runtime;
			$( $parsed_modules :: $parsed_name $( < $parsed_generic > )*),*;
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
		$( $parsed_modules:ident :: $parsed_name:ident $( < $parsed_generic:ident > )* ),*;
		$name:ident: $module:ident::{}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		$crate::__decl_outer_config!(
			$runtime;
			$( $parsed_modules :: $parsed_name $( < $parsed_generic > )*),*;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( <$rest_modules_generic> )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$( $parsed_modules:ident :: $parsed_name:ident $( < $parsed_generic:ident > )* ),*;
		;
	) => {
		$crate::paste::item! {
			$crate::runtime_primitives::impl_outer_config!(
				pub struct GenesisConfig for $runtime {
					$(
						[< $parsed_name Config >] => $parsed_modules $( < $parsed_generic > )*,
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
			$ingore:ident $( ( $( $ignor:ident )* ) )*
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
