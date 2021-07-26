// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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
		VestingSchedule,
	},
	fungible, fungibles,
	imbalance::{Imbalance, OnUnbalanced, SignedImbalance},
	BalanceStatus, ExistenceRequirement, WithdrawReasons,
};

mod members;
pub use members::{
	All, AsContains, ChangeMembers, Contains, ContainsLengthBound, InitializeMembers, IsInVec,
	SortedMembers,
};

mod validation;
pub use validation::{
	EstimateNextNewSession, EstimateNextSessionRotation, FindAuthor, KeyOwnerProofSystem, Lateness,
	OneSessionHandler, ValidatorRegistration, ValidatorSet, ValidatorSetWithIdentification,
	VerifySeal,
};

mod filter;
pub use filter::{
	AllowAll, ClearFilterGuard, DenyAll, Filter, FilterStack, FilterStackGuard, InstanceFilter,
	IntegrityTest,
};

mod misc;
pub use misc::{
	Backing, ConstU32, EnsureInherentsAreFirst, EstimateCallFee, ExecuteBlock, ExtrinsicCall, Get,
	GetBacking, GetDefault, HandleLifetime, IsSubType, IsType, Len, OffchainWorker,
	OnKilledAccount, OnNewAccount, SameOrOther, Time, TryDrop, UnixTime,
};

mod stored_map;
pub use stored_map::{StorageMapShim, StoredMap};
mod randomness;
pub use randomness::Randomness;

mod metadata;
pub use metadata::{
	CallMetadata, GetCallMetadata, GetCallName, GetPalletVersion, PalletInfo, PalletInfoAccess,
	PalletVersion, PALLET_VERSION_STORAGE_KEY_POSTFIX,
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
pub use dispatch::{EnsureOrigin, OriginTrait, UnfilteredDispatchable};

mod voting;
pub use voting::{CurrencyToVote, SaturatingCurrencyToVote, U128CurrencyToVote};
