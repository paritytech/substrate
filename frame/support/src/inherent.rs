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
pub use sp_inherents::{InherentData, ProvideInherent, CheckInherentsResult, IsFatalError};


/// Implement the outer inherent.
/// All given modules need to implement `ProvideInherent`.
///
/// The order will be the order of created inherent and the enforced order of inherent in block
/// extrinsics.
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
///
/// `timestamp` will provide and check for the first extrinsic, `consensus` for the second and
/// `aura` for the third.
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
					let inherent = $module::create_inherent(self);
					inherents.push($uncheckedextrinsic::new(
						inherent.into(),
						None,
					).expect("Runtime UncheckedExtrinsic is not Opaque, \
						so it has to return `Some`; qed"));
				)*

				inherents
			}

			fn check_extrinsics(&self, block: &$block) -> $crate::inherent::CheckInherentsResult {
				use $crate::inherent::{ProvideInherent, IsFatalError};
				use $crate::traits::IsSubType;
				use $crate::sp_runtime::traits::Block as _;

				let mut result = $crate::inherent::CheckInherentsResult::new();

				let xts = block.extrinsics();

				$(
					match xts.next() {
						Some(xt) => {
							if xt.signature.is_some() {
								todo!("return fatal error invalid inherent is signed");
							}

							if let Some(call) = IsSubType::<_>::is_sub_type(&xt.function) {
								if let Err(e) = $module::check_inherent(call, self) {
									result.put_error(
										$module::INHERENT_IDENTIFIER, &e
									).expect("There is only one fatal error; qed");
									if e.is_fatal_error() {
										return result
									}
								}
							} else {
								todo!("return fatal error invalid inherent is for different pallet");
							}
						}
						None => {
							todo!("return fatal error invalid inherent is missing");
						}
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
		Something,
		SomethingElse,
	}

	#[derive(codec::Encode, codec::Decode, Clone, PartialEq, Eq, Debug, serde::Serialize)]
	enum CallTest2 {
		Something,
	}

	struct ModuleTest;
	impl ProvideInherent for ModuleTest {
		type Call = CallTest;
		type Error = sp_inherents::MakeFatalError<()>;
		const INHERENT_IDENTIFIER: sp_inherents::InherentIdentifier = *b"test1235";

		fn create_inherent(_: &InherentData) -> Option<Self::Call> {
			Some(CallTest::Something)
		}

		fn check_inherent(call: &Self::Call, _: &InherentData) -> Result<(), Self::Error> {
			match call {
				CallTest::Something => Ok(()),
				CallTest::SomethingElse => Err(().into()),
			}
		}
	}

	struct ModuleTest2;
	impl ProvideInherent for ModuleTest2 {
		type Call = CallTest2;
		type Error = sp_inherents::MakeFatalError<()>;
		const INHERENT_IDENTIFIER: sp_inherents::InherentIdentifier = *b"test1234";

		fn create_inherent(_: &InherentData) -> Option<Self::Call> {
			Some(CallTest2::Something)
		}

		fn is_inherent_required(_: &InherentData) -> Result<Option<Self::Error>, Self::Error> { 
			Ok(Some(().into()))
		}
	}

	type Block = testing::Block<Extrinsic>;

	#[derive(codec::Encode, codec::Decode, Clone, PartialEq, Eq, Debug, serde::Serialize)]
	struct Extrinsic {
		function: Call,
	}

	impl traits::Extrinsic for Extrinsic {
		type Call = Call;
		type SignaturePayload = ();

		fn new(function: Call, _: Option<()>) -> Option<Self> {
			Some(Self { function })
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
			Extrinsic { function: Call::Test(CallTest::Something) },
			Extrinsic { function: Call::Test2(CallTest2::Something) },
		];
		assert_eq!(expected, inherents);
	}

	#[test]
	fn check_inherents_works() {
		let block = Block::new(
			Header::new_from_number(1),
			vec![
				Extrinsic { function: Call::Test2(CallTest2::Something) },
				Extrinsic { function: Call::Test(CallTest::Something) },
			],
		);

		assert!(InherentData::new().check_extrinsics(&block).ok());

		let block = Block::new(
			Header::new_from_number(1),
			vec![
				Extrinsic { function: Call::Test2(CallTest2::Something) },
				Extrinsic { function: Call::Test(CallTest::SomethingElse) },
			],
		);

		assert!(InherentData::new().check_extrinsics(&block).fatal_error());
	}

	#[test]
	fn required_inherents_enforced() {
		let block = Block::new(
			Header::new_from_number(1),
			vec![Extrinsic { function: Call::Test(CallTest::Something) }],
		);

		assert!(InherentData::new().check_extrinsics(&block).fatal_error());
	}
}
