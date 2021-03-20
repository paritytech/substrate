// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Macros for generating the runtime genesis config.

/// Helper macro for `impl_outer_config`
#[macro_export]
macro_rules! __impl_outer_config_types {
	// Generic + Instance
	(
		$concrete:ident $config:ident $snake:ident { $instance:ident } < $ignore:ident >;
		$( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig<$concrete, $snake::$instance>;
		$crate::__impl_outer_config_types! { $concrete $( $rest )* }
	};
	// Generic
	(
		$concrete:ident $config:ident $snake:ident < $ignore:ident >;
		$( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig<$concrete>;
		$crate::__impl_outer_config_types! { $concrete $( $rest )* }
	};
	// No Generic and maybe Instance
	(
		$concrete:ident $config:ident $snake:ident $( { $instance:ident } )?;
		$( $rest:tt )*
	) => {
		#[cfg(any(feature = "std", test))]
		pub type $config = $snake::GenesisConfig;
		$crate::__impl_outer_config_types! { $concrete $( $rest )* }
	};
	($concrete:ident) => ()
}

/// Implement the runtime genesis configuration.
///
/// This combines all pallet genesis configurations into one runtime
/// specific genesis configuration.
///
/// ```ignore
/// pub struct GenesisConfig for Runtime where AllPalletsWithSystem = AllPalletsWithSystem {
/// 	rust_module_one: Option<ModuleOneConfig>,
/// 	...
/// }
/// ```
#[macro_export]
macro_rules! impl_outer_config {
	(
		pub struct $main:ident for $concrete:ident where
			AllPalletsWithSystem = $all_pallets_with_system:ident
		{
			$( $config:ident =>
				$snake:ident $( $instance:ident )? $( <$generic:ident> )*, )*
		}
	) => {
		$crate::__impl_outer_config_types! {
			$concrete $( $config $snake $( { $instance } )? $( <$generic> )*; )*
		}

		$crate::paste::item! {
			#[cfg(any(feature = "std", test))]
			#[derive($crate::serde::Serialize, $crate::serde::Deserialize, Default)]
			#[serde(rename_all = "camelCase")]
			#[serde(deny_unknown_fields)]
			pub struct $main {
				$(
					pub [< $snake $(_ $instance )? >]: $config,
				)*
			}
			#[cfg(any(feature = "std", test))]
			impl $crate::sp_runtime::BuildStorage for $main {
				fn assimilate_storage(
					&self,
					storage: &mut $crate::sp_runtime::Storage,
				) -> std::result::Result<(), String> {
					$(
						$crate::impl_outer_config! {
							@CALL_FN
							$concrete;
							$snake;
							$( $instance )?;
							&self.[< $snake $(_ $instance )? >];
							storage;
						}
					)*

					$crate::BasicExternalities::execute_with_storage(storage, || {
						<$all_pallets_with_system as $crate::traits::OnGenesis>::on_genesis();
					});

					Ok(())
				}
			}
		}
	};
	(@CALL_FN
		$runtime:ident;
		$module:ident;
		$instance:ident;
		$extra:expr;
		$storage:ident;
	) => {
		$crate::sp_runtime::BuildModuleGenesisStorage::<$runtime, $module::$instance>::build_module_genesis_storage(
			$extra,
			$storage,
		)?;
	};
	(@CALL_FN
		$runtime:ident;
		$module:ident;
		;
		$extra:expr;
		$storage:ident;
	) => {
		$crate::sp_runtime::BuildModuleGenesisStorage::
			<$runtime, $module::__InherentHiddenInstance>::build_module_genesis_storage(
				$extra,
				$storage,
			)?;
	}
}
