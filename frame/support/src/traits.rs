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

//! Traits and associated utilities for use in the FRAME environment.
//!
//! NOTE: If you're looking for `parameter_types`, it has moved in to the top-level module.

pub mod tokens;
pub use tokens::{
	currency::{
		ActiveIssuanceOf, Currency, LockIdentifier, LockableCurrency, NamedReservableCurrency,
		ReservableCurrency, TotalIssuanceOf, VestingSchedule,
	},
	fungible, fungibles,
	imbalance::{Imbalance, OnUnbalanced, SignedImbalance},
	nonfungible, nonfungibles, BalanceStatus, ExistenceRequirement, Locker, WithdrawReasons,
};

mod members;
#[allow(deprecated)]
pub use members::{AllowAll, DenyAll, Filter};
pub use members::{
	AsContains, ChangeMembers, Contains, ContainsLengthBound, ContainsPair, Everything,
	EverythingBut, FromContainsPair, InitializeMembers, InsideBoth, IsInVec, Nothing,
	RankedMembers, SortedMembers, TheseExcept,
};

mod validation;
pub use validation::{
	DisabledValidators, EstimateNextNewSession, EstimateNextSessionRotation, FindAuthor,
	KeyOwnerProofSystem, Lateness, OneSessionHandler, ValidatorRegistration, ValidatorSet,
	ValidatorSetWithIdentification, VerifySeal,
};

mod error;
pub use error::PalletError;

mod filter;
pub use filter::{ClearFilterGuard, FilterStack, FilterStackGuard, InstanceFilter};

mod misc;
pub use misc::{
	defensive_prelude::{self, *},
	AccountTouch, Backing, ConstBool, ConstI128, ConstI16, ConstI32, ConstI64, ConstI8, ConstU128,
	ConstU16, ConstU32, ConstU64, ConstU8, DefensiveMax, DefensiveMin, DefensiveSaturating,
	DefensiveTruncateFrom, EnsureInherentsAreFirst, EqualPrivilegeOnly, EstimateCallFee,
	ExecuteBlock, ExtrinsicCall, Get, GetBacking, GetDefault, HandleLifetime, IsSubType, IsType,
	Len, OffchainWorker, OnKilledAccount, OnNewAccount, PrivilegeCmp, SameOrOther, Time,
	TryCollect, TryDrop, TypedGet, UnixTime, WrapperKeepOpaque, WrapperOpaque,
};
#[allow(deprecated)]
pub use misc::{PreimageProvider, PreimageRecipient};
#[doc(hidden)]
pub use misc::{DEFENSIVE_OP_INTERNAL_ERROR, DEFENSIVE_OP_PUBLIC_ERROR};

mod stored_map;
pub use stored_map::{StorageMapShim, StoredMap};
mod randomness;
pub use randomness::Randomness;

mod metadata;
pub use metadata::{
	CallMetadata, CrateVersion, GetCallIndex, GetCallMetadata, GetCallName, GetStorageVersion,
	NoStorageVersionSet, PalletInfo, PalletInfoAccess, PalletInfoData, PalletsInfoAccess,
	StorageVersion, STORAGE_VERSION_STORAGE_KEY_POSTFIX,
};

mod hooks;
pub use hooks::{
	GenesisBuild, Hooks, IntegrityTest, OnFinalize, OnGenesis, OnIdle, OnInitialize,
	OnRuntimeUpgrade, OnTimestampSet,
};

pub mod schedule;
mod storage;
pub use storage::{
	Incrementable, Instance, PartialStorageInfoTrait, StorageInfo, StorageInfoTrait,
	StorageInstance, TrackedStorageKey, WhitelistedStorageKeys,
};

mod dispatch;
#[allow(deprecated)]
pub use dispatch::EnsureOneOf;
pub use dispatch::{
	AsEnsureOriginWithArg, CallerTrait, EitherOf, EitherOfDiverse, EnsureOrigin,
	EnsureOriginEqualOrHigherPrivilege, EnsureOriginWithArg, MapSuccess, NeverEnsureOrigin,
	OriginTrait, TryMapSuccess, UnfilteredDispatchable,
};

mod voting;
pub use voting::{
	ClassCountOf, CurrencyToVote, PollStatus, Polling, SaturatingCurrencyToVote,
	U128CurrencyToVote, VoteTally,
};

mod preimages;
pub use preimages::{Bounded, BoundedInline, FetchResult, Hash, QueryPreimage, StorePreimage};

mod messages;
pub use messages::{
	EnqueueMessage, ExecuteOverweightError, Footprint, NoopServiceQueues, ProcessMessage,
	ProcessMessageError, ServiceQueues, TransformOrigin,
};

#[cfg(feature = "try-runtime")]
mod try_runtime;
#[cfg(feature = "try-runtime")]
pub use try_runtime::{Select as TryStateSelect, TryState, UpgradeCheckSelect};
