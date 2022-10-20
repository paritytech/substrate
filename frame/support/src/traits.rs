// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Traits and associated utilities for use in the FRAME environment.
//!
//! NOTE: If you're looking for `parameter_types`, it has moved in to the top-level module.

pub mod tokens;
pub use tokens::{
	currency::{
		Currency, LockIdentifier, LockableCurrency, NamedReservableCurrency, ReservableCurrency,
		TotalIssuanceOf, VestingSchedule,
	},
	fungible, fungibles,
	imbalance::{Imbalance, OnUnbalanced, SignedImbalance},
	BalanceStatus, ExistenceRequirement, WithdrawReasons,
};

mod members;
#[allow(deprecated)]
pub use members::{AllowAll, DenyAll, Filter};
pub use members::{
	AsContains, ChangeMembers, Contains, ContainsLengthBound, Everything, InitializeMembers,
	IsInVec, Nothing, SortedMembers,
};

mod validation;
pub use validation::{
	DisabledValidators, EstimateNextNewSession, EstimateNextSessionRotation, FindAuthor,
	KeyOwnerProofSystem, Lateness, OneSessionHandler, ValidatorRegistration, ValidatorSet,
	ValidatorSetWithIdentification, VerifySeal,
};

mod filter;
pub use filter::{ClearFilterGuard, FilterStack, FilterStackGuard, InstanceFilter, IntegrityTest};

mod misc;
pub use misc::{
	defensive_prelude::{self, *},
	Backing, ConstBool, ConstI128, ConstI16, ConstI32, ConstI64, ConstI8, ConstU128, ConstU16,
	ConstU32, ConstU64, ConstU8, DefensiveSaturating, EnsureInherentsAreFirst, EqualPrivilegeOnly,
	EstimateCallFee, ExecuteBlock, ExtrinsicCall, Get, GetBacking, GetDefault, HandleLifetime,
	IsSubType, IsType, Len, OffchainWorker, OnKilledAccount, OnNewAccount, PreimageProvider,
	PreimageRecipient, PrivilegeCmp, SameOrOther, Time, TryCollect, TryDrop, UnixTime,
	WrapperKeepOpaque, WrapperOpaque,
};

mod stored_map;
pub use stored_map::{StorageMapShim, StoredMap};
mod randomness;
pub use randomness::Randomness;

mod metadata;
pub use metadata::{
	CallMetadata, CrateVersion, GetCallMetadata, GetCallName, GetStorageVersion, PalletInfo,
	PalletInfoAccess, PalletInfoData, PalletsInfoAccess, StorageVersion,
	STORAGE_VERSION_STORAGE_KEY_POSTFIX,
};

mod hooks;
#[cfg(feature = "std")]
pub use hooks::GenesisBuild;
pub use hooks::{
	Hooks, OnFinalize, OnGenesis, OnIdle, OnInitialize, OnRuntimeUpgrade, OnTimestampSet,
};
#[cfg(feature = "try-runtime")]
pub use hooks::{OnRuntimeUpgradeHelpersExt, ON_RUNTIME_UPGRADE_PREFIX};

pub mod schedule;
mod storage;
pub use storage::{
	Instance, PartialStorageInfoTrait, StorageInfo, StorageInfoTrait, StorageInstance,
};

mod dispatch;
pub use dispatch::{EnsureOneOf, EnsureOrigin, OriginTrait, UnfilteredDispatchable};

mod voting;
pub use voting::{
	CurrencyToVote, PollStatus, Polling, SaturatingCurrencyToVote, U128CurrencyToVote, VoteTally,
};
