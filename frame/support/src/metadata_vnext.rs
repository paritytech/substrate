// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

pub use frame_metadata::vnext;

#[macro_export]
macro_rules! impl_runtime_metadata_vnext {
	(
		for $runtime:ident with modules where Extrinsic = $ext:ident
			$( $rest:tt )*
	) => {
		impl $runtime {
			pub fn metadata_vnext() -> $crate::metadata::vnext::RuntimeMetadataPrefixed<$crate::scale_info::form::CompactForm> {
				let mut registry = $crate::scale_info::Registry::new();
				let metadata =
					$crate::metadata::vnext::RuntimeMetadataLastVersion {
							modules: $crate::__runtime_modules_to_metadata_vnext!($runtime;; $( $rest )*),
							// extrinsic: $crate::metadata::ExtrinsicMetadata {
							// 	version: <$ext as $crate::sp_runtime::traits::ExtrinsicMetadata>::VERSION,
							// 	signed_extensions: <
							// 			<
							// 				$ext as $crate::sp_runtime::traits::ExtrinsicMetadata
							// 			>::SignedExtensions as $crate::sp_runtime::traits::SignedExtension
							// 		>::identifier()
							// 			.into_iter()
							// 			.map($crate::metadata::DecodeDifferent::Encode)
							// 			.collect(),
							// },
					};
				use $crate::scale_info::IntoCompact as _;
				metadata.into_compact(&mut registry).into()
			}
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata_vnext {
	(
		$runtime: ident;
		$( $metadata:expr ),*;
		$mod:ident::$module:ident $( < $instance:ident > )? as $name:ident
			{ index $index:tt }
			$(with)+ $($kw:ident)*
		,
		$( $rest:tt )*
	) => {
		$crate::__runtime_modules_to_metadata_vnext!(
			$runtime;
			$( $metadata, )* $crate::metadata::vnext::ModuleMetadata {
				name: stringify!($name),
				// index: $index,
				// storage: $crate::__runtime_modules_to_metadata_calls_storage!(
				// 	$mod, $module $( <$instance> )?, $runtime, $(with $kw)*
				// ),
				calls: $crate::__runtime_modules_to_metadata_calls_call_vnext!(
					$mod, $module $( <$instance> )?, $runtime, $(with $kw)*
				),
				event: $crate::__runtime_modules_to_metadata_calls_event_vnext!(
					$mod, $module $( <$instance> )?, $runtime, $(with $kw)*
				),
				// constants: $crate::metadata::DecodeDifferent::Encode(
				// 	$crate::metadata::FnEncode(
				// 		$mod::$module::<$runtime $(, $mod::$instance )?>::module_constants_metadata
				// 	)
				// ),
				// errors: $crate::metadata::DecodeDifferent::Encode(
				// 	$crate::metadata::FnEncode(
				// 		<$mod::$module::<$runtime $(, $mod::$instance )?> as $crate::metadata::ModuleErrorMetadata>::metadata
				// 	)
				// )
			};
			$( $rest )*
		)
	};
	(
		$runtime:ident;
		$( $metadata:expr ),*;
	) => {
		vec![$( $metadata ),* ]
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata_calls_call_vnext {
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with Call
		$(with $kws:ident)*
	) => {
		Some($mod::$module::<$runtime $(, $mod::$instance )?>::call_functions_vnext())
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
		$crate::__runtime_modules_to_metadata_calls_call_vnext! {
			$mod, $module $( <$instance> )?, $runtime, $(with $kws)*
		};
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
	) => {
		None
	};
}


#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata_calls_event_vnext {
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with Event
		$(with $kws:ident)*
	) => {
		Some($crate::paste::expr!{
				$runtime:: [< __module_events_vnext_ $mod $(_ $instance)?>]()
			}
		)
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
		$crate::__runtime_modules_to_metadata_calls_event_vnext!( $mod, $module $( <$instance> )?, $runtime, $(with $kws)* );
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
	) => {
		None
	};
}

// #[macro_export]
// #[doc(hidden)]
// macro_rules! __runtime_modules_to_metadata_calls_storage_vnext {
// 	(
// 		$mod: ident,
// 		$module: ident $( <$instance:ident> )?,
// 		$runtime: ident,
// 		with Storage
// 		$(with $kws:ident)*
// 	) => {
// 		Some($crate::metadata::DecodeDifferent::Encode(
// 			$crate::metadata::FnEncode(
// 				$mod::$module::<$runtime $(, $mod::$instance )?>::storage_metadata
// 			)
// 		))
// 	};
// 	(
// 		$mod: ident,
// 		$module: ident $( <$instance:ident> )?,
// 		$runtime: ident,
// 		with $_:ident
// 		$(with $kws:ident)*
// 	) => {
// 		$crate::__runtime_modules_to_metadata_calls_storage! {
// 			$mod, $module $( <$instance> )?, $runtime, $(with $kws)*
// 		};
// 	};
// 	(
// 		$mod: ident,
// 		$module: ident $( <$instance:ident> )?,
// 		$runtime: ident,
// 	) => {
// 		None
// 	};
// }
