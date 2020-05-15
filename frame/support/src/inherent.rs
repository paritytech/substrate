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

#[doc(hidden)]
pub use crate::sp_std::vec::Vec;
#[doc(hidden)]
pub use crate::sp_runtime::traits::{Block as BlockT, Extrinsic};
#[doc(hidden)]
pub use sp_inherents::{InherentData, ProvideInherent, CheckInherentsResult, IsFatalError};


/// Implement the outer inherent.
/// All given modules need to implement `ProvideInherent`.
///
/// # Example
///
/// ```nocompile
/// impl_outer_inherent! {
///     impl Inherents where Block = Block, UncheckedExtrinsic = UncheckedExtrinsic {
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
		impl Inherents for $runtime:ident where
			Block = $block:ident,
			UncheckedExtrinsic = $uncheckedextrinsic:ident
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
				use $crate::inherent::{ProvideInherent, Extrinsic};

				let mut inherents = Vec::new();

				$(
					if let Some(inherent) = $module::create_inherent(self) {
						inherents.push($uncheckedextrinsic::new(
							inherent.into(),
							None,
						).expect("Runtime UncheckedExtrinsic is not Opaque, so it has to return `Some`; qed"));
					}
				)*

				inherents
			}

			fn check_extrinsics(&self, block: &$block) -> $crate::inherent::CheckInherentsResult {
				use $crate::inherent::{ProvideInherent, IsFatalError};
				use $crate::dispatch::IsSubType;

				let mut result = $crate::inherent::CheckInherentsResult::new();
				for xt in block.extrinsics() {
					if $crate::inherent::Extrinsic::is_signed(xt).unwrap_or(false) {
						break
					}

					$({
						if let Some(call) = IsSubType::<_>::is_sub_type(&xt.function) {
							if let Err(e) = $module::check_inherent(call, self) {
								result.put_error(
									$module::INHERENT_IDENTIFIER, &e
								).expect("There is only one fatal error; qed");
								if e.is_fatal_error() {
									return result
								}
							}
						}
					})*
				}

				$(
					match $module::is_inherent_required(self) {
						Ok(Some(e)) => {
							let found = block.extrinsics().iter().any(|xt| {
								if $crate::inherent::Extrinsic::is_signed(xt).unwrap_or(false) {
									return false
								}

								let call: Option<&<$module as ProvideInherent>::Call> =
									xt.function.is_sub_type();

								call.is_some()
							});

							if !found {
								result.put_error(
									$module::INHERENT_IDENTIFIER, &e
								).expect("There is only one fatal error; qed");
								if e.is_fatal_error() {
									return result
								}
							}
						},
						Ok(None) => (),
						Err(e) => {
							result.put_error(
								$module::INHERENT_IDENTIFIER, &e
							).expect("There is only one fatal error; qed");
							if e.is_fatal_error() {
								return result
							}
						},
					}
				)*

				result
			}
		}
	};
}
