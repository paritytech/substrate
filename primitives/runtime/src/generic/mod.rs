// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

// tag::description[]
//! Generic implementations of Extrinsic/Header/Block.
// end::description[]

mod block;
mod checked_extrinsic;
mod digest;
mod era;
mod header;
#[cfg(test)]
mod tests;
mod unchecked_extrinsic;

pub use self::{
	block::{Block, BlockId, SignedBlock},
	checked_extrinsic::CheckedExtrinsic,
	digest::{Digest, DigestItem, DigestItemRef, OpaqueDigestItemId},
	era::{Era, Phase},
	header::Header,
	unchecked_extrinsic::{SignedPayload, UncheckedExtrinsic},
};
