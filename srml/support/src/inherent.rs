// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#[doc(hidden)]
pub use crate::rstd::vec::Vec;
#[doc(hidden)]
pub use crate::runtime_primitives::traits::{Block as BlockT, Extrinsic};
#[doc(hidden)]
pub use inherents::{InherentData, ProvideInherent, CheckInherentsResult, IsFatalError};


/// Implement the outer inherent.
/// All given modules need to implement `ProvideInherent`.
///
/// # Example
///
/// ```nocompile
/// impl_outer_inherent! {
///     pub struct InherentData where Block = Block, UncheckedExtrinsic = UncheckedExtrinsic {
///         timestamp: Timestamp,
///         consensus: Consensus,
///         /// Aura module using the `Timestamp` call.
///         aura: Timestamp,
///     }
/// }
/// ```
#[macro_export]
macro_rules! impl_outer_inherent {
	(
		impl Inherents where Block = $block:ident, UncheckedExtrinsic = $uncheckedextrinsic:ident
		{
			$( $module:ident: $call:ident, )*
		}
	) => {
		trait InherentDataExt {
			fn create_extrinsics(&self) ->
				$crate::inherent::Vec<<$block as $crate::inherent::BlockT>::Extrinsic>;
			fn check_extrinsics(&self, block: &$block) -> $crate::inherent::CheckInherentsResult;
		}

		impl InherentDataExt for $crate::inherent::InherentData {
			fn create_extrinsics(&self) ->
				$crate::inherent::Vec<<$block as $crate::inherent::BlockT>::Extrinsic> {
				use $crate::inherent::ProvideInherent;

				let mut inherents = Vec::new();

				$(
					if let Some(inherent) = $module::create_inherent(self) {
						inherents.push($uncheckedextrinsic::new_unsigned(
							Call::$call(inherent))
						);
					}
				)*

				inherents
			}

			fn check_extrinsics(&self, block: &$block) -> $crate::inherent::CheckInherentsResult {
				use $crate::inherent::{ProvideInherent, IsFatalError};

				let mut result = $crate::inherent::CheckInherentsResult::new();
				for xt in block.extrinsics() {
					if $crate::inherent::Extrinsic::is_signed(xt).unwrap_or(false) {
						break;
					}

					$(
						match xt.function {
							Call::$call(ref call) => {
								if let Err(e) = $module::check_inherent(call, self) {
									result.put_error(
										$module::INHERENT_IDENTIFIER, &e
									).expect("There is only one fatal error; qed");
									if e.is_fatal_error() {
										return result;
									}
								}
							}
							_ => {},
						}
					)*
				}

				result
			}
		}
	};
}
