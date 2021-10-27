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

//! Common traits and types that are useful for describing staking

use crate::{traits::Get, CloneNoBound, EqNoBound, PartialEqNoBound, WeakBoundedVec};
use codec::{Decode, Encode, MaxEncodedLen};
use sp_runtime::Perbill;
use sp_staking::{
	offence::{Offence, OffenceError},
	SessionIndex,
};

/// A trait for decoupling offence reporters from the actual handling of offence reports.
pub trait ReportOffence<Reporter, Offender, O: Offence<Offender>, MaxReportersCount: Get<u32>> {
	/// Report an `offence` and reward given `reporters`.
	fn report_offence(
		reporters: WeakBoundedVec<Reporter, MaxReportersCount>,
		offence: O,
	) -> Result<(), OffenceError>;

	/// Returns true iff all of the given offenders have been previously reported
	/// at the given time slot. This function is useful to prevent the sending of
	/// duplicate offence reports.
	fn is_known_offence(offenders: &[Offender], time_slot: &O::TimeSlot) -> bool;
}

impl<Reporter, Offender, O: Offence<Offender>, MaxReportersCount: Get<u32>>
	ReportOffence<Reporter, Offender, O, MaxReportersCount> for ()
{
	fn report_offence(
		_reporters: WeakBoundedVec<Reporter, MaxReportersCount>,
		_offence: O,
	) -> Result<(), OffenceError> {
		Ok(())
	}

	fn is_known_offence(_offenders: &[Offender], _time_slot: &O::TimeSlot) -> bool {
		true
	}
}

/// A trait to take action on an offence.
///
/// Used to decouple the module that handles offences and
/// the one that should punish for those offences.
pub trait OnOffenceHandler<
	Reporter: MaxEncodedLen + Clone + Eq + sp_std::fmt::Debug,
	Offender: MaxEncodedLen + Clone + Eq + sp_std::fmt::Debug,
	Res,
	MaxReportersCount: Get<u32>,
>
{
	/// A handler for an offence of a particular kind.
	///
	/// Note that this contains a list of all previous offenders
	/// as well. The implementer should cater for a case, where
	/// the same authorities were reported for the same offence
	/// in the past (see `OffenceCount`).
	///
	/// The vector of `slash_fraction` contains `Perbill`s
	/// the authorities should be slashed and is computed
	/// according to the `OffenceCount` already. This is of the same length as `offenders.`
	/// Zero is a valid value for a fraction.
	///
	/// The `session` parameter is the session index of the offence.
	///
	/// The receiver might decide to not accept this offence. In this case, the call site is
	/// responsible for queuing the report and re-submitting again.
	fn on_offence(
		offenders: &[OffenceDetails<Reporter, Offender, MaxReportersCount>],
		slash_fraction: &[Perbill],
		session: SessionIndex,
	) -> Res;
}

impl<
		Reporter: MaxEncodedLen + Clone + Eq + sp_std::fmt::Debug,
		Offender: MaxEncodedLen + Clone + Eq + sp_std::fmt::Debug,
		Res: Default,
		MaxReportersCount: Get<u32>,
	> OnOffenceHandler<Reporter, Offender, Res, MaxReportersCount> for ()
{
	fn on_offence(
		_offenders: &[OffenceDetails<Reporter, Offender, MaxReportersCount>],
		_slash_fraction: &[Perbill],
		_session: SessionIndex,
	) -> Res {
		Default::default()
	}
}

/// A details about an offending authority for a particular kind of offence.
/// `MaxReportersCount` bounds weakly the number of reporters
#[derive(
	CloneNoBound,
	PartialEqNoBound,
	EqNoBound,
	Encode,
	Decode,
	MaxEncodedLen,
	frame_support::RuntimeDebugNoBound,
	scale_info::TypeInfo,
)]
#[codec(mel_bound(MaxReportersCount: Get<u32>))]
#[scale_info(skip_type_params(MaxReportersCount))]
pub struct OffenceDetails<
	Reporter: MaxEncodedLen + Clone + Eq + sp_std::fmt::Debug,
	Offender: MaxEncodedLen + Clone + Eq + sp_std::fmt::Debug,
	MaxReportersCount: Get<u32>,
> {
	/// The offending authority id
	pub offender: Offender,
	/// A list of reporters of offences of this authority ID. Possibly empty where there are no
	/// particular reporters.
	pub reporters: WeakBoundedVec<Reporter, MaxReportersCount>,
}
