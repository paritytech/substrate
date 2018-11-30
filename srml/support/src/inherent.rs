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
pub use runtime_primitives::{
	traits::{ProvideInherent, Block as BlockT}, CheckInherentError, InherentData
};


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
		pub struct $name:ident where Block = $block:ident {
			$( $module:ident: $module_ty:ident, )*
		}
	) => {
		impl_outer_inherent!(
			$( #[$attr] )*
			pub struct $name where Block = $block, Call = Call {
				$( $module: $module_ty, )*
			}
		);
	};
	(
		$(#[$attr:meta])*
		pub struct $name:ident where Block = $block:ident {
			$( $module:ident: $module_ty:ident, )*
		}
	) => {
		impl_outer_inherent!(
			$( #[$attr] )*
			pub struct $name where Block = $block, Call = Call {
				$( $module: $module_ty, )*
			}
		);
	};
	(
		$(#[$attr:meta])*
		pub struct $name:ident where Block = $block:ident, Call = $call:ident {
			$( $module:ident: $module_ty:ident, )*
		}
	) => {
		$( #[$attr] )*
		#[derive(Encode, Decode)]
		/// Inherent data to include in a block.
		pub struct $name {
			$( $module: <$module_ty as $crate::inherent::ProvideInherent>::Inherent, )*
		}

		impl $name {
			/// Create a new instance.
			pub fn new( $( $module: <$module_ty as $crate::inherent::ProvideInherent>::Inherent ),* ) -> Self {
				Self {
					$( $module, )*
				}
			}

			fn check_inherents(
				data: $crate::inherent::InherentData,
				block: $block
			) -> $crate::inherent::Result<(), $crate::inherent::CheckInherentError> {
				$(
					<$module_ty as $crate::inherent::ProvideInherent>::check_inherent(
						&block, data.$module, &|xt| match xt.function {
							Call::$module_ty(ref data) => Some(data),
							_ => None,
						})?;
				)*
				Ok(())
			}
		}
	};
}
