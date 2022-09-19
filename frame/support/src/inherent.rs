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

pub use sp_inherents::{
	InherentData, CheckInherentsResult, IsFatalError, InherentIdentifier, MakeFatalError,
};

/// A pallet that provides or verifies an inherent extrinsic.
///
/// The pallet may provide the inherent, verify an inherent, or both provide and verify.
pub trait ProvideInherent {
	/// The call type of the pallet.
	type Call;
	/// The error returned by `check_inherent`.
	type Error: codec::Encode + IsFatalError;
	/// The inherent identifier used by this inherent.
	const INHERENT_IDENTIFIER: self::InherentIdentifier;

	/// Create an inherent out of the given `InherentData`.
	fn create_inherent(data: &InherentData) -> Option<Self::Call>;

	/// Determines whether this inherent is required in this block.
	///
	/// - `Ok(None)` indicates that this inherent is not required in this block. The default
	/// implementation returns this.
	///
	/// - `Ok(Some(e))` indicates that this inherent is required in this block. The
	/// `impl_outer_inherent!`, will call this function from its `check_extrinsics`.
	/// If the inherent is not present, it will return `e`.
	///
	/// - `Err(_)` indicates that this function failed and further operations should be aborted.
	///
	/// NOTE: If inherent is required then the runtime asserts that the block contains at least
	/// one inherent for which:
	/// * type is [`Self::Call`],
	/// * [`Self::is_inherent`] returns true.
	fn is_inherent_required(_: &InherentData) -> Result<Option<Self::Error>, Self::Error> { Ok(None) }

	/// Check whether the given inherent is valid. Checking the inherent is optional and can be
	/// omitted by using the default implementation.
	///
	/// When checking an inherent, the first parameter represents the inherent that is actually
	/// included in the block by its author. Whereas the second parameter represents the inherent
	/// data that the verifying node calculates.
	///
	/// NOTE: A block can contains multiple inherent.
	fn check_inherent(_: &Self::Call, _: &InherentData) -> Result<(), Self::Error> {
		Ok(())
	}

	/// Return whether the call is an inherent call.
	///
	/// NOTE: Signed extrinsics are not inherent, but signed extrinsic with the given call variant
	/// can be dispatched.
	///
	/// # Warning
	///
	/// In FRAME, inherent are enforced to be before other extrinsics, for this reason,
	/// pallets with unsigned transactions **must ensure** that no unsigned transaction call
	/// is an inherent call, when implementing `ValidateUnsigned::validate_unsigned`.
	/// Otherwise block producer can produce invalid blocks by including them after non inherent.
	fn is_inherent(call: &Self::Call) -> bool;
}

/// Implement the outer inherent.
/// All given modules need to implement [`ProvideInherent`].
///
/// # Example
///
/// ```nocompile
/// impl_outer_inherent! {
///     impl Inherents where
///         Block = Block,
///         UncheckedExtrinsic = UncheckedExtrinsic,
///         Runtime = Runtime,
///     {
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
			UncheckedExtrinsic = $uncheckedextrinsic:ident,
			Runtime = $runtime:ident,
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
				use $crate::inherent::ProvideInherent;

				let mut inherents = Vec::new();

				$(
					if let Some(inherent) = $module::create_inherent(self) {
						let inherent = <$uncheckedextrinsic as $crate::inherent::Extrinsic>::new(
							inherent.into(),
							None,
						).expect("Runtime UncheckedExtrinsic is not Opaque, so it has to return \
							`Some`; qed");

						inherents.push(inherent);
					}
				)*

				inherents
			}

			fn check_extrinsics(&self, block: &$block) -> $crate::inherent::CheckInherentsResult {
				use $crate::inherent::{ProvideInherent, IsFatalError};
				use $crate::traits::{IsSubType, ExtrinsicCall};
				use $crate::sp_runtime::traits::Block as _;

				let mut result = $crate::inherent::CheckInherentsResult::new();

				for xt in block.extrinsics() {
					// Inherents are before any other extrinsics.
					// And signed extrinsics are not inherents.
					if $crate::inherent::Extrinsic::is_signed(xt).unwrap_or(false) {
						break
					}

					let mut is_inherent = false;

					$({
						let call = <$uncheckedextrinsic as ExtrinsicCall>::call(xt);
						if let Some(call) = IsSubType::<_>::is_sub_type(call) {
							if $module::is_inherent(call) {
								is_inherent = true;
								if let Err(e) = $module::check_inherent(call, self) {
									result.put_error(
										$module::INHERENT_IDENTIFIER, &e
									).expect("There is only one fatal error; qed");
									if e.is_fatal_error() {
										return result
									}
								}
							}
						}
					})*

					// Inherents are before any other extrinsics.
					// No module marked it as inherent thus it is not.
					if !is_inherent {
						break
					}
				}

				$(
					match $module::is_inherent_required(self) {
						Ok(Some(e)) => {
							let found = block.extrinsics().iter().any(|xt| {
								let is_signed = $crate::inherent::Extrinsic::is_signed(xt)
									.unwrap_or(false);

								if !is_signed {
									let call = <
										$uncheckedextrinsic as ExtrinsicCall
									>::call(xt);
									if let Some(call) = IsSubType::<_>::is_sub_type(call) {
										$module::is_inherent(&call)
									} else {
										false
									}
								} else {
									// Signed extrinsics are not inherents.
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

		impl $crate::traits::EnsureInherentsAreFirst<$block> for $runtime {
			fn ensure_inherents_are_first(block: &$block) -> Result<(), u32> {
				use $crate::inherent::ProvideInherent;
				use $crate::traits::{IsSubType, ExtrinsicCall};
				use $crate::sp_runtime::traits::Block as _;

				let mut first_signed_observed = false;

				for (i, xt) in block.extrinsics().iter().enumerate() {
					let is_signed = $crate::inherent::Extrinsic::is_signed(xt).unwrap_or(false);

					let is_inherent = if is_signed {
						// Signed extrinsics are not inherents.
						false
					} else {
						let mut is_inherent = false;
						$({
							let call = <$uncheckedextrinsic as ExtrinsicCall>::call(xt);
							if let Some(call) = IsSubType::<_>::is_sub_type(call) {
								if $module::is_inherent(&call) {
									is_inherent = true;
								}
							}
						})*
						is_inherent
					};

					if !is_inherent {
						first_signed_observed = true;
					}

					if first_signed_observed && is_inherent {
						return Err(i as u32)
					}
				}

				Ok(())
			}
		}
	};
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::{traits, testing::{Header, self}};

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

	impl crate::traits::IsSubType<CallTest> for Call {
		fn is_sub_type(&self) -> Option<&CallTest> {
			match self {
				Self::Test(test) => Some(test),
				_ => None,
			}
		}
	}

	impl crate::traits::IsSubType<CallTest2> for Call {
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
				_ => unreachable!("other calls are not inherents"),
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

	impl crate::traits::ExtrinsicCall for Extrinsic {
		fn call(&self) -> &Self::Call {
			&self.function
		}
	}

	parity_util_mem::malloc_size_of_is_0!(Extrinsic);

	struct Runtime;

	impl_outer_inherent! {
		impl Inherents where
			Block = Block,
			UncheckedExtrinsic = Extrinsic,
			Runtime = Runtime,
		{
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

		assert_eq!(
			InherentData::new().check_extrinsics(&block).into_errors().collect::<Vec<_>>(),
			vec![(*b"test1234", vec![])],
		);
	}

	#[test]
	fn inherent_first_works() {
		use crate::traits::EnsureInherentsAreFirst;
		let block = Block::new(
			Header::new_from_number(1),
			vec![
				Extrinsic { function: Call::Test2(CallTest2::RequiredInherent), signed: false },
				Extrinsic { function: Call::Test(CallTest::OptionalInherent(true)), signed: false },
				Extrinsic { function: Call::Test(CallTest::NotInherent), signed: false },
				Extrinsic { function: Call::Test(CallTest::NotInherent), signed: false },
			],
		);

		assert!(Runtime::ensure_inherents_are_first(&block).is_ok());
	}

	#[test]
	fn inherent_cannot_be_placed_after_non_inherent() {
		use crate::traits::EnsureInherentsAreFirst;
		let block = Block::new(
			Header::new_from_number(1),
			vec![
				Extrinsic { function: Call::Test2(CallTest2::RequiredInherent), signed: false },
				Extrinsic { function: Call::Test(CallTest::NotInherent), signed: false },
				// This inherent is placed after non inherent: invalid
				Extrinsic { function: Call::Test(CallTest::OptionalInherent(true)), signed: false },
			],
		);

		assert_eq!(Runtime::ensure_inherents_are_first(&block).err().unwrap(), 2);

		let block = Block::new(
			Header::new_from_number(1),
			vec![
				Extrinsic { function: Call::Test2(CallTest2::RequiredInherent), signed: false },
				Extrinsic { function: Call::Test(CallTest::OptionalInherent(true)), signed: true },
				// This inherent is placed after non inherent: invalid
				Extrinsic { function: Call::Test(CallTest::OptionalInherent(true)), signed: false },
			],
		);

		assert_eq!(Runtime::ensure_inherents_are_first(&block).err().unwrap(), 2);
	}
}
