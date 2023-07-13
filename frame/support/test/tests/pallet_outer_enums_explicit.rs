// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use frame_support::{derive_impl, traits::ConstU32};

mod common;

use common::outer_enums::{pallet, pallet2};

pub type Header = sp_runtime::generic::Header<u32, sp_runtime::traits::BlakeTwo256>;
pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, RuntimeCall, (), ()>;

#[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::DefaultConfig)]
impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type Block = Block;
	type BlockHashCount = ConstU32<10>;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type OnSetCode = ();
}

impl common::outer_enums::pallet::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
}
impl common::outer_enums::pallet::Config<common::outer_enums::pallet::Instance1> for Runtime {
	type RuntimeEvent = RuntimeEvent;
}
impl common::outer_enums::pallet2::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
}
impl common::outer_enums::pallet2::Config<common::outer_enums::pallet::Instance1> for Runtime {
	type RuntimeEvent = RuntimeEvent;
}
impl common::outer_enums::pallet3::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
}
impl common::outer_enums::pallet3::Config<common::outer_enums::pallet::Instance1> for Runtime {
	type RuntimeEvent = RuntimeEvent;
}

frame_support::construct_runtime!(
	pub struct Runtime
	{
		// Exclude part `Storage` in order not to check its metadata in tests.
		System: frame_system::{Pallet, Config<T>, Call, Event<T> },

		// This pallet exposes the Error type explicitly.
		Example: common::outer_enums::pallet::{Pallet, Config<T>, Event<T>, Error<T>},
		Instance1Example: common::outer_enums::pallet::<Instance1>::{ Pallet, Config<T>, Event<T> },

		// This pallet does not mention the Error type, but it must be propagated (similarly to the polkadot/kusama).
		Example2: common::outer_enums::pallet2::{Pallet, Config<T>, Event<T> },
		Instance1Example2: common::outer_enums::pallet2::<Instance1>::{Pallet, Config<T>, Event<T>},

		// This pallet does not declare any errors.
		Example3: common::outer_enums::pallet3::{Pallet, Config<T>, Event<T>},
		Instance1Example3: common::outer_enums::pallet3::<Instance1>::{Pallet, Config<T>, Event<T>},
	}
);

#[test]
fn module_error_outer_enum_expand_explicit() {
	// The Runtime has *all* parts explicitly defined.

	// Check that all error types are propagated
	match RuntimeError::Example(pallet::Error::InsufficientProposersBalance) {
		// Error passed implicitely to the pallet system.
		RuntimeError::System(system) => match system {
			frame_system::Error::InvalidSpecName => (),
			frame_system::Error::SpecVersionNeedsToIncrease => (),
			frame_system::Error::FailedToExtractRuntimeVersion => (),
			frame_system::Error::NonDefaultComposite => (),
			frame_system::Error::NonZeroRefCount => (),
			frame_system::Error::CallFiltered => (),
			frame_system::Error::__Ignore(_, _) => (),
		},

		// Error declared explicitly.
		RuntimeError::Example(example) => match example {
			pallet::Error::InsufficientProposersBalance => (),
			pallet::Error::NonExistentStorageValue => (),
			pallet::Error::__Ignore(_, _) => (),
		},
		// Error declared explicitly.
		RuntimeError::Instance1Example(example) => match example {
			pallet::Error::InsufficientProposersBalance => (),
			pallet::Error::NonExistentStorageValue => (),
			pallet::Error::__Ignore(_, _) => (),
		},

		// Error must propagate even if not defined explicitly as pallet part.
		RuntimeError::Example2(example) => match example {
			pallet2::Error::OtherInsufficientProposersBalance => (),
			pallet2::Error::OtherNonExistentStorageValue => (),
			pallet2::Error::__Ignore(_, _) => (),
		},
		// Error must propagate even if not defined explicitly as pallet part.
		RuntimeError::Instance1Example2(example) => match example {
			pallet2::Error::OtherInsufficientProposersBalance => (),
			pallet2::Error::OtherNonExistentStorageValue => (),
			pallet2::Error::__Ignore(_, _) => (),
		},
	};
}
