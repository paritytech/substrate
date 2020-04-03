// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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
pub use crate::sp_runtime::traits::ValidateUnsigned;
#[doc(hidden)]
pub use crate::sp_runtime::transaction_validity::{
	TransactionValidity, UnknownTransaction, TransactionValidityError, TransactionSource,
};


/// Implement `ValidateUnsigned` for `Runtime`.
/// All given modules need to implement `ValidateUnsigned`.
///
/// # Example
///
/// ```
/// # mod timestamp {
/// # 	pub struct Module;
/// #
/// # 	impl frame_support::unsigned::ValidateUnsigned for Module {
/// # 		type Call = Call;
/// #
/// # 		fn validate_unsigned(_source: frame_support::unsigned::TransactionSource, _call: &Self::Call)
/// 			-> frame_support::unsigned::TransactionValidity {
/// # 			unimplemented!();
/// # 		}
/// # 	}
/// #
/// # 	pub enum Call {
/// # 	}
/// # }
/// #
/// # pub type Timestamp = timestamp::Module;
/// #
/// #
/// # pub enum Call {
/// # 	Timestamp(timestamp::Call),
/// # }
/// # #[allow(unused)]
/// pub struct Runtime;
///
/// frame_support::impl_outer_validate_unsigned! {
/// 	impl ValidateUnsigned for Runtime {
/// 		Timestamp
/// 	}
/// }
/// ```
#[macro_export]
macro_rules! impl_outer_validate_unsigned {
	(
		impl ValidateUnsigned for $runtime:ident {
			$( $module:ident )*
		}
	) => {
		impl $crate::unsigned::ValidateUnsigned for $runtime {
			type Call = Call;

			fn pre_dispatch(call: &Self::Call) -> Result<(), $crate::unsigned::TransactionValidityError> {
				#[allow(unreachable_patterns)]
				match call {
					$( Call::$module(inner_call) => $module::pre_dispatch(inner_call), )*
					// pre-dispatch should not stop inherent extrinsics, validation should prevent
					// including arbitrary (non-inherent) extrinsics to blocks.
					_ => Ok(()),
				}
			}

			fn validate_unsigned(
				#[allow(unused_variables)]
				source: $crate::unsigned::TransactionSource,
				call: &Self::Call,
			) -> $crate::unsigned::TransactionValidity {
				#[allow(unreachable_patterns)]
				match call {
					$( Call::$module(inner_call) => $module::validate_unsigned(source, inner_call), )*
					_ => $crate::unsigned::UnknownTransaction::NoUnsignedValidator.into(),
				}
			}
		}
	};
}

#[cfg(test)]
mod test_empty_call {
	pub enum Call {}

	#[allow(unused)]
	pub struct Runtime;

	impl_outer_validate_unsigned! {
		impl ValidateUnsigned for Runtime {
		}
	}
}

#[cfg(test)]
mod test_partial_and_full_call {
	pub mod timestamp {
		pub struct Module;

		impl super::super::ValidateUnsigned for Module {
			type Call = Call;

			fn validate_unsigned(
				_source: super::super::TransactionSource,
				_call: &Self::Call
			) -> super::super::TransactionValidity {
				unimplemented!();
			}
		}

		pub enum Call {
			Foo,
		}
	}

	mod test_full_unsigned {
		pub type Timestamp = super::timestamp::Module;

		pub enum Call {
			Timestamp(super::timestamp::Call),
		}

		pub struct Runtime;

		impl_outer_validate_unsigned! {
			impl ValidateUnsigned for Runtime {
				Timestamp
			}
		}

		#[test]
		fn used() {
			let _ = Call::Timestamp(super::timestamp::Call::Foo);
			let _ = Runtime;
		}
	}

	mod test_not_full_unsigned {
		pub enum Call {
			Timestamp(super::timestamp::Call),
		}

		pub struct Runtime;

		impl_outer_validate_unsigned! {
			impl ValidateUnsigned for Runtime {
			}
		}

		#[test]
		fn used() {
			let _ = Call::Timestamp(super::timestamp::Call::Foo);
			let _ = Runtime;
		}
	}
}
