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

#[doc(hidden)]
pub use rstd::{result::Result, vec::Vec};
#[doc(hidden)]
pub use runtime_primitives::traits::ProvideInherent;


/// Implement the outer inherent.
/// All given modules need to implement `ProvideInherent`.
///
/// # Example
///
/// ```nocompile
/// impl_outer_inherent! {
///     pub struct InherentData where Block = Block, UncheckedExtrinsic = UncheckedExtrinsic {
///         timestamp: Timestamp export Error as TimestampInherentError,
///         consensus: Consensus,
///     }
/// }
/// ```
///
/// Additional parameters after `UncheckedExtrinsic` are `Error` and `Call`.
#[macro_export]
macro_rules! impl_outer_inherent {
	(
		$(#[$attr:meta])*
		pub struct $name:ident where Block = $block:ident, UncheckedExtrinsic = $unchecked:ident {
			$( $module:ident: $module_ty:ident $(export Error as $error_name:ident)*, )*
		}
	) => {
		impl_outer_inherent!(
			$( #[$attr] )*
			pub struct $name where Block = $block, UncheckedExtrinsic = $unchecked, Error = InherentError, Call = Call {
				$( $module: $module_ty $(export Error as $error_name)*, )*
			}
		);
	};
	(
		$(#[$attr:meta])*
		pub struct $name:ident where Block = $block:ident, UncheckedExtrinsic = $unchecked:ident, Error = $error:ident {
			$( $module:ident: $module_ty:ident $(export Error as $error_name:ident)*, )*
		}
	) => {
		impl_outer_inherent!(
			$( #[$attr] )*
			pub struct $name where Block = $block, UncheckedExtrinsic = $unchecked, Error = $error, Call = Call {
				$( $module: $module_ty $(export Error as $error_name)*, )*
			}
		);
	};
	(
		$(#[$attr:meta])*
		pub struct $name:ident where Block = $block:ident, UncheckedExtrinsic = $unchecked:ident, Error = $error:ident, Call = $call:ident {
			$( $module:ident: $module_ty:ident $(export Error as $error_name:ident)*, )*
		}
	) => {
		$( #[$attr] )*
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Encode, Decode)]
		/// Inherent data to include in a block.
		pub struct $name {
			$( $module: <$module_ty as $crate::inherent::ProvideInherent>::Inherent, )*
		}

		$(
			$(
				pub type $error_name =<$module_ty as $crate::inherent::ProvideInherent>::Error;
			)*
		)*

		impl $name {
			/// Create a new instance.
			pub fn new( $( $module: <$module_ty as $crate::inherent::ProvideInherent>::Inherent ),* ) -> Self {
				Self {
					$( $module, )*
				}
			}

			fn create_inherent_extrinsics(self) -> Vec<$unchecked> {
				let mut inherent = $crate::inherent::Vec::new();

				$(
					inherent.extend(
						<$module_ty as $crate::inherent::ProvideInherent>::create_inherent_extrinsics(self.$module)
							.into_iter()
							.map(|v| (v.0, $unchecked::new_unsigned($call::$module_ty(v.1))))
					);
				)*

				inherent.as_mut_slice().sort_unstable_by_key(|v| v.0);
				inherent.into_iter().map(|v| v.1).collect()
			}

			fn check_inherents(self, block: $block) -> $crate::inherent::Result<(), $error> {
				$(
					<$module_ty as $crate::inherent::ProvideInherent>::check_inherent(
						&block, self.$module, &|xt| match xt.function {
							Call::$module_ty(ref data) => Some(data),
							_ => None,
						}).map_err($error::$module_ty)?;
				)*
				Ok(())
			}
		}

		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Encode)]
		#[cfg_attr(feature = "std", derive(Decode))]
		pub enum $error {
			$( $module_ty(<$module_ty as $crate::inherent::ProvideInherent>::Error), )*
		}
	};
}
