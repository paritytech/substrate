// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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
pub use sp_inherents::{
	InherentData, ProvideInherent, CheckInherentsResult, IsFatalError, InherentIdentifier,
	MakeFatalError,
};

/// The identifier for runtime inherent errors.
///
/// The associated error is a `String`.
pub const RUNTIME_INHERENT_IDENTIFIER: InherentIdentifier = *b"RuntimeI";

/// Implement the outer inherent.
/// All given modules need to implement `ProvideInherent`.
///
/// # Example
///
/// ```nocompile
/// impl_outer_inherent! {
///     impl Inherents where Block = Block, UncheckedExtrinsic = UncheckedExtrinsic {
///         timestamp,
///         consensus,
///         aura,
///     }
/// }
/// ```
#[macro_export]
macro_rules! impl_outer_inherent {
	(
		impl Inherents where
			Block = $block:ident,
			UncheckedExtrinsic = $uncheckedextrinsic:ident
		{
			$( $module:ident, )*
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
				use $crate::traits::IsSubType;
				use $crate::sp_runtime::traits::Block as _;

				let mut result = $crate::inherent::CheckInherentsResult::new();

				let mut checking_for_inherents = true;
				for xt in block.extrinsics() {
					let is_signed = $crate::inherent::Extrinsic::is_signed(xt).unwrap_or(false);

					let is_inherent = if is_signed {
						false
					} else {
						let mut is_inherent = false;
						$({
							if let Some(call) = IsSubType::<_>::is_sub_type(&xt.function) {
								if $module::is_inherent(&call) {
									is_inherent = true;
								}
							}
						})*
						is_inherent
					};

					match (checking_for_inherents, is_inherent) {
						(true, true) => {
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
						},
						(true, false) => checking_for_inherents = false,
						(false, true) => {
							let e = $crate::inherent::MakeFatalError::from(
								"Invalid inherent position: inherents must be before all other \
								extrinsics in the block".as_bytes(),
							);
							result.put_error(
								$crate::inherent::RUNTIME_INHERENT_IDENTIFIER,
								&e,
							).expect("There is only one fatal error; qed");
							return result
						},
						(false, false) => (),
					}
				}

				$(
					match $module::is_inherent_required(self) {
						Ok(Some(e)) => {
							let found = block.extrinsics().iter().any(|xt| {
								let is_signed = $crate::inherent::Extrinsic::is_signed(xt)
									.unwrap_or(false);

								if !is_signed {
									if let Some(call) = IsSubType::<_>::is_sub_type(&xt.function) {
										$module::is_inherent(&call)
									} else {
										false
									}
								} else {
									false
								}
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

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::{traits, testing::{Header, self}};
	use crate::traits::IsSubType;
	use codec::Encode;

	#[derive(codec::Encode, codec::Decode, Clone, PartialEq, Eq, Debug, serde::Serialize)]
	enum Call {
		Test(CallTest),
		Test2(CallTest2),
	}

	impl From<CallTest> for Call {
		fn from(call: CallTest) -> Self {
			Self::Test(call)
		}
	}

	impl From<CallTest2> for Call {
		fn from(call: CallTest2) -> Self {
			Self::Test2(call)
		}
	}

	impl IsSubType<CallTest> for Call {
		fn is_sub_type(&self) -> Option<&CallTest> {
			match self {
				Self::Test(test) => Some(test),
				_ => None,
			}
		}
	}

	impl IsSubType<CallTest2> for Call {
		fn is_sub_type(&self) -> Option<&CallTest2> {
			match self {
				Self::Test2(test) => Some(test),
				_ => None,
			}
		}
	}

	#[derive(codec::Encode, codec::Decode, Clone, PartialEq, Eq, Debug, serde::Serialize)]
	enum CallTest {
		OptionalInherent(bool),
		NotInherent,
	}

	#[derive(codec::Encode, codec::Decode, Clone, PartialEq, Eq, Debug, serde::Serialize)]
	enum CallTest2 {
		RequiredInherent,
	}

	struct ModuleTest;
	impl ProvideInherent for ModuleTest {
		type Call = CallTest;
		type Error = sp_inherents::MakeFatalError<()>;
		const INHERENT_IDENTIFIER: sp_inherents::InherentIdentifier = *b"test1235";

		fn create_inherent(_: &InherentData) -> Option<Self::Call> {
			Some(CallTest::OptionalInherent(true))
		}

		fn check_inherent(call: &Self::Call, _: &InherentData) -> Result<(), Self::Error> {
			match call {
				CallTest::OptionalInherent(true) => Ok(()),
				CallTest::OptionalInherent(false) => Err(().into()),
				_ => Ok(())
			}
		}

		fn is_inherent(call: &Self::Call) -> bool {
			matches!(call, CallTest::OptionalInherent(_))
		}
	}

	struct ModuleTest2;
	impl ProvideInherent for ModuleTest2 {
		type Call = CallTest2;
		type Error = sp_inherents::MakeFatalError<()>;
		const INHERENT_IDENTIFIER: sp_inherents::InherentIdentifier = *b"test1234";

		fn create_inherent(_: &InherentData) -> Option<Self::Call> {
			Some(CallTest2::RequiredInherent)
		}

		fn is_inherent_required(_: &InherentData) -> Result<Option<Self::Error>, Self::Error> {
			Ok(Some(().into()))
		}

		fn is_inherent(call: &Self::Call) -> bool {
			matches!(call, CallTest2::RequiredInherent)
		}
	}

	type Block = testing::Block<Extrinsic>;

	#[derive(codec::Encode, codec::Decode, Clone, PartialEq, Eq, Debug, serde::Serialize)]
	struct Extrinsic {
		signed: bool,
		function: Call,
	}

	impl traits::Extrinsic for Extrinsic {
		type Call = Call;
		type SignaturePayload = ();

		fn new(function: Call, signed_data: Option<()>) -> Option<Self> {
			Some(Self {
				function,
				signed: signed_data.is_some(),
			})
		}

		fn is_signed(&self) -> Option<bool> {
			Some(self.signed)
		}
	}

	parity_util_mem::malloc_size_of_is_0!(Extrinsic);

	impl_outer_inherent! {
		impl Inherents where Block = Block, UncheckedExtrinsic = Extrinsic {
			ModuleTest,
			ModuleTest2,
		}
	}

	#[test]
	fn create_inherents_works() {
		let inherents = InherentData::new().create_extrinsics();

		let expected = vec![
			Extrinsic { function: Call::Test(CallTest::OptionalInherent(true)), signed: false },
			Extrinsic { function: Call::Test2(CallTest2::RequiredInherent), signed: false },
		];
		assert_eq!(expected, inherents);
	}

	#[test]
	fn check_inherents_works() {
		let block = Block::new(
			Header::new_from_number(1),
			vec![
				Extrinsic { function: Call::Test2(CallTest2::RequiredInherent), signed: false },
				Extrinsic { function: Call::Test(CallTest::OptionalInherent(true)), signed: false },
			],
		);

		assert!(InherentData::new().check_extrinsics(&block).ok());

		let block = Block::new(
			Header::new_from_number(1),
			vec![
				Extrinsic { function: Call::Test2(CallTest2::RequiredInherent), signed: false },
				Extrinsic { function: Call::Test(CallTest::OptionalInherent(false)), signed: false },
			],
		);

		assert!(InherentData::new().check_extrinsics(&block).fatal_error());
	}

	#[test]
	fn required_inherents_enforced() {
		let block = Block::new(
			Header::new_from_number(1),
			vec![
				Extrinsic { function: Call::Test(CallTest::OptionalInherent(true)), signed: false }
			],
		);

		assert!(InherentData::new().check_extrinsics(&block).fatal_error());
	}

	#[test]
	fn inherent_first_works() {
		let block = Block::new(
			Header::new_from_number(1),
			vec![
				Extrinsic { function: Call::Test2(CallTest2::RequiredInherent), signed: false },
				Extrinsic { function: Call::Test(CallTest::OptionalInherent(true)), signed: false },
				Extrinsic { function: Call::Test(CallTest::NotInherent), signed: false },
				Extrinsic { function: Call::Test(CallTest::NotInherent), signed: false },
			],
		);

		assert!(InherentData::new().check_extrinsics(&block).ok());
	}

	#[test]
	fn signed_are_not_inherent() {
		let block = Block::new(
			Header::new_from_number(1),
			vec![
				Extrinsic { function: Call::Test2(CallTest2::RequiredInherent), signed: false },
				// NOTE: checking this call would fail, but it is not checked as it is not an
				// inherent, because it is signed.
				Extrinsic { function: Call::Test(CallTest::OptionalInherent(false)), signed: true },
			],
		);

		assert!(InherentData::new().check_extrinsics(&block).ok());

		let block = Block::new(
			Header::new_from_number(1),
			vec![
				// NOTE: this is not considered an inherent, thus block is failing because of
				// missing required inherent.
				Extrinsic { function: Call::Test2(CallTest2::RequiredInherent), signed: true },
			],
		);

		assert!(InherentData::new().check_extrinsics(&block).fatal_error());
	}

	#[test]
	fn inherent_cannot_be_placed_after_non_inherent() {
		let block = Block::new(
			Header::new_from_number(1),
			vec![
				Extrinsic { function: Call::Test2(CallTest2::RequiredInherent), signed: false },
				Extrinsic { function: Call::Test(CallTest::NotInherent), signed: false },
				Extrinsic { function: Call::Test(CallTest::OptionalInherent(true)), signed: false },
			],
		);

		let err_msg = "Invalid inherent position: inherents must be before all other extrinsics in \
			the block".as_bytes().encode();
		assert_eq!(
			InherentData::new().check_extrinsics(&block).into_errors().collect::<Vec<_>>(),
			vec![(RUNTIME_INHERENT_IDENTIFIER, err_msg)],
		);
	}
}
