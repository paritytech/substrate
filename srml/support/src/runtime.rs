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

/// Construct a runtime, with the given name and the given modules.
///
/// # Example:
///
/// ```nocompile
/// construct_runtime!(
///     pub enum Runtime with Log(interalIdent: DigestItem<SessionKey>) where
///         Block = Block,
///         NodeBlock = runtime::Block
///     {
///         System: system,
///         Test: test::{default, Log(Test)},
///         Test2: test_with_long_module::{Module},
///     }
/// )
/// ```
///
/// The module `System: system` will expand to `System: system::{Module, Call, Storage, Event<T>, Config}`.
/// The identifier `System` is the name of the module and the lower case identifier `system` is the
/// name of the rust module for this module.
/// The module `Test: test::{default, Log(Test)}` will expand to
/// `Test: test::{Module, Call, Storage, Event<T>, Config, Log(Test)}`.
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
#[macro_export]
macro_rules! construct_runtime {
	(
		pub enum $runtime:ident with Log ($log_internal:ident: DigestItem<$( $log_genarg:ty ),+>)
			where
				Block = $block:ident,
				NodeBlock = $node_block:ty
		{
			$( $rest:tt )*
		}
	) => {
		construct_runtime!(
			$runtime;
			$block;
			$node_block;
			$log_internal < $( $log_genarg ),* >;
			;
			$( $rest )*
		);
	};
	(
		$runtime:ident;
		$block:ident;
		$node_block:ty;
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
	(
		$runtime:ident;
		$block:ident;
		$node_block:ty;
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
		mashup! {
			$(
				substrate_generate_ident_name["config-ident" $name] = $name Config;
				substrate_generate_ident_name["inherent-error-ident" $name] = $name InherentError;
			)*
		}

		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		pub struct $runtime;
		impl $crate::runtime_primitives::traits::GetNodeBlockType for $runtime {
			type NodeBlock = $node_block;
		}
		impl $crate::runtime_primitives::traits::GetRuntimeBlockType for $runtime {
			type RuntimeBlock = $block;
		}
		__decl_outer_event!(
			$runtime;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*
		);
		__decl_outer_origin!(
			$runtime;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*
		);
		__decl_all_modules!(
			$runtime;
			;
			;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*;
		);
		__decl_outer_dispatch!(
			$runtime;
			;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*;
		);
		__decl_runtime_metadata!(
			$runtime;
			;
			;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*;
		);
		__decl_outer_log!(
			$runtime;
			$log_internal < $( $log_genarg ),* >;
			;
			$(
				$name: $module::{ $( $modules $( ( $( $modules_args ),* ) )* ),* }
			),*;
		);
		__decl_outer_config!(
			$runtime;
			;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*;
		);
		__decl_outer_inherent!(
			$runtime;
			$block;
			;
			$(
				$name: $module::{ $( $modules $( <$modules_generic> )* ),* }
			),*;
		);
	}
}

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
				System: $module:ident::{
					$ingore:ident $d( <$ignor:ident> )* $d(, $modules:ident $d( <$modules_generic:ident> )* )*
				}
				$d(, $rest_name:ident : $rest_module:ident::{
					$d( $rest_modules:ident $d( <$rest_modules_generic:ident> )* ),*
				})*
			) => {
				$macro_name!(
					$runtime;
					$module;
					;
					$d(
						$rest_name: $rest_module::{
							$d( $rest_modules $d( <$rest_modules_generic> )* ),*
						}
					),*;
				);
			};
			(
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
				$macro_name!(
					$runtime;
					$module;
					$d( $parsed_modules $d( <$parsed_generic> )* ),*;
					$d(
						$rest_name: $rest_module::{
							$d( $rest_modules $d( <$rest_modules_generic> )* ),*
						}
					)*;
				);
			};
			(
				$runtime:ident;
				$name:ident: $module:ident::{
					$ingore:ident $d( <$ignor:ident> )* $d(, $modules:ident $d( <$modules_generic:ident> )* )*
				}
				$d(, $rest_name:ident : $rest_module:ident::{
					$d( $rest_modules:ident $d( <$rest_modules_generic:ident> )* ),*
				})*
			) => {
				$macro_name!(
					$runtime;
					;
					;
					$name: $module::{ $d( $modules $d( <$modules_generic> )* ),* }
					$d(
						, $rest_name: $rest_module::{
							$d( $rest_modules $d( <$rest_modules_generic> )* ),*
						}
					)*;
				);
			};
			(
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
				$macro_name!(
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
			(
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
				$macro_name!(
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
			(
				$runtime:ident;
				$d( $system:ident )*;
				$d( $parsed_modules:ident $d( <$parsed_generic:ident> )* ),*;
				$name:ident: $module:ident::{}
				$d(, $rest_name:ident : $rest_module:ident::{
					$d( $rest_modules:ident $d( <$rest_modules_generic:ident> )* ),*
				})*;
			) => {
				$macro_name!(
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
			(
				$runtime:ident;
				$d( $system:ident )+;
				$d( $parsed_modules:ident $d( <$parsed_generic:ident> )* ),*;
				;
			) => {
				$macro_outer_name! {
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
		__decl_all_modules!(
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
		__decl_all_modules!(
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
		__decl_all_modules!(
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
		__decl_all_modules!(
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
		__decl_outer_dispatch!(
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
		__decl_outer_dispatch!(
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
		__decl_outer_dispatch!(
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
		__decl_outer_dispatch!(
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
		impl_outer_dispatch!(
			pub enum Call for $runtime where origin: Origin {
				$( $parsed_modules::$parsed_name, )*
			}
		);
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __decl_runtime_metadata {
	(
		$runtime:ident;
		;
		$( $parsed_modules:ident { Module $( with $parsed_storage:ident )* } ),*;
		$name:ident: $module:ident::{
			Module $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		__decl_runtime_metadata!(
			$runtime;
			$module { Module, };
			$( $parsed_modules { Module $( with $parsed_storage )* } ),*;
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
		$current_module:ident { , Storage };
		$( $parsed_modules:ident { Module $( with $parsed_storage:ident )* } ),*;
		$name:ident: $module:ident::{
			Module $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		__decl_runtime_metadata!(
			$runtime;
			;
			$( $parsed_modules { Module $( with $parsed_storage )* }, )* $module { Module with Storage };
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( <$rest_modules_generic> )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		;
		$( $parsed_modules:ident { Module $( with $parsed_storage:ident )* } ),*;
		$name:ident: $module:ident::{
			Storage $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		__decl_runtime_metadata!(
			$runtime;
			$module { , Storage };
			$( $parsed_modules { Module $( with $parsed_storage )* } ),*;
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
		$current_module:ident { Module, };
		$( $parsed_modules:ident { Module $( with $parsed_storage:ident )* } ),*;
		$name:ident: $module:ident::{
			Storage $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		__decl_runtime_metadata!(
			$runtime;
			;
			$( $parsed_modules { Module $( with $parsed_storage )* }, )* $module { Module with Storage };
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( <$rest_modules_generic> )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$( $current_module:ident { $( $current_module_storage:tt )* } )*;
		$( $parsed_modules:ident { Module $( with $parsed_storage:ident )* } ),*;
		$name:ident: $module:ident::{
			$ingore:ident $( <$ignor:ident> )* $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
				$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
			})*;
	) => {
		__decl_runtime_metadata!(
			$runtime;
			$( $current_module { $( $current_module_storage )* } )*;
			$( $parsed_modules { Module $( with $parsed_storage )* } ),*;
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
		$current_module:ident { Module, };
		$( $parsed_modules:ident { Module $( with $parsed_storage:ident )* } ),*;
		$name:ident: $module:ident::{}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		__decl_runtime_metadata!(
			$runtime;
			;
			$( $parsed_modules { Module $( with $parsed_storage )* }, )* $module { Module };
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( <$rest_modules_generic> )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		$( $current_module:ident { $( $ignore:tt )* } )*;
		$( $parsed_modules:ident { Module $( with $parsed_storage:ident )* } ),*;
		$name:ident: $module:ident::{}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		__decl_runtime_metadata!(
			$runtime;
			;
			$( $parsed_modules { Module $( with $parsed_storage )* } ),*;
			$(
				$rest_name: $rest_module::{
					$( $rest_modules $( <$rest_modules_generic> )* ),*
				}
			),*;
		);
	};
	(
		$runtime:ident;
		;
		$( $parsed_modules:ident { Module $( with $parsed_storage:ident )* } ),*;
		;
	) => {
		impl_runtime_metadata!(
			for $runtime with modules
				$( $parsed_modules::Module $(with $parsed_storage)*, )*
		);
	}
}
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
		__decl_outer_log!(
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
		__decl_outer_log!(
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
		__decl_outer_log!(
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
		impl_outer_log!(
			pub enum Log($log_internal: DigestItem<$( $log_genarg ),*>) for $runtime {
				$( $parsed_modules ( $( $parsed_args ),* ) ),*
			}
		);
	};
}

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
		__decl_outer_config!(
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
		__decl_outer_config!(
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
		__decl_outer_config!(
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
		__decl_outer_config!(
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
		substrate_generate_ident_name! {
			impl_outer_config!(
				pub struct GenesisConfig for $runtime {
					$(
						"config-ident" $parsed_name => $parsed_modules $( < $parsed_generic > )*,
					)*
				}
			);
		}
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __decl_outer_inherent {
	(
		$runtime:ident;
		$block:ident;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		$name:ident: $module:ident::{
			Inherent $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		__decl_outer_inherent!(
			$runtime;
			$block;
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
		$block:ident;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		$name:ident: $module:ident::{
			$ingore:ident $( <$ignor:ident> )* $(, $modules:ident $( <$modules_generic:ident> )* )*
		}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		__decl_outer_inherent!(
			$runtime;
			$block;
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
		$block:ident;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		$name:ident: $module:ident::{}
		$(, $rest_name:ident : $rest_module:ident::{
			$( $rest_modules:ident $( <$rest_modules_generic:ident> )* ),*
		})*;
	) => {
		__decl_outer_inherent!(
			$runtime;
			$block;
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
		$block:ident;
		$( $parsed_modules:ident :: $parsed_name:ident ),*;
		;
	) => {
		substrate_generate_ident_name! {
			impl_outer_inherent!(
				pub struct InherentData where Block = $block {
					$(
						$parsed_modules: $parsed_name,
					)*
				}
			);
		}
	};
}
