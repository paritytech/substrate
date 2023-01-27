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

//! Re-exports `sp-weights` public API, and contains benchmarked weight constants specific to FRAME.

mod block_weights;
mod extrinsic_weights;
mod paritydb_weights;
mod rocksdb_weights;

use crate::dispatch;
pub use sp_weights::*;

/// These constants are specific to FRAME, and the current implementation of its various components.
/// For example: FRAME System, FRAME Executive, our FRAME support libraries, etc...
pub mod constants {
	pub use sp_weights::constants::*;

	// Expose the Block and Extrinsic base weights.
	pub use super::{block_weights::BlockExecutionWeight, extrinsic_weights::ExtrinsicBaseWeight};

	// Expose the DB weights.
	pub use super::{
		paritydb_weights::constants::ParityDbWeight, rocksdb_weights::constants::RocksDbWeight,
	};
}

#[deprecated = "Function has moved to `frame_support::dispatch`"]
pub fn extract_actual_pays_fee(
	res: &dispatch::DispatchResultWithPostInfo,
	info: &dispatch::DispatchInfo,
) -> dispatch::Pays {
	dispatch::extract_actual_pays_fee(res, info)
}
#[deprecated = "Function has moved to `frame_support::dispatch`"]
pub fn extract_actual_weight(
	res: &dispatch::DispatchResultWithPostInfo,
	info: &dispatch::DispatchInfo,
) -> Weight {
	dispatch::extract_actual_weight(res, info)
}
#[deprecated = "Trait has moved to `frame_support::dispatch`"]
pub trait ClassifyDispatch<T>: dispatch::ClassifyDispatch<T> {
	fn classify_dispatch(&self, target: T) -> dispatch::DispatchClass {
		<Self as dispatch::ClassifyDispatch<T>>::classify_dispatch(self, target)
	}
}
#[deprecated = "Enum has moved to `frame_support::dispatch`"]
pub type DispatchClass = dispatch::DispatchClass;
#[deprecated = "Struct has moved to `frame_support::dispatch`"]
pub type DispatchInfo = dispatch::DispatchInfo;
#[deprecated = "Trait has moved to `frame_support::dispatch`"]
pub trait GetDispatchInfo: dispatch::GetDispatchInfo {
	fn get_dispatch_info(&self) -> dispatch::DispatchInfo {
		<Self as dispatch::GetDispatchInfo>::get_dispatch_info(self)
	}
}
#[deprecated = "Trait has moved to `frame_support::dispatch`"]
pub trait OneOrMany<T>: dispatch::OneOrMany<T> {
	fn into_iter(self) -> Self::Iter
	where
		Self: Sized,
	{
		<Self as dispatch::OneOrMany<T>>::into_iter(self)
	}
}
#[deprecated = "Enum has moved to `frame_support::dispatch`"]
pub type Pays = dispatch::Pays;
#[deprecated = "Trait has moved to `frame_support::dispatch`"]
pub trait PaysFee<T>: dispatch::PaysFee<T> {
	fn pays_fee(&self, target: T) -> dispatch::Pays {
		<Self as dispatch::PaysFee<T>>::pays_fee(self, target)
	}
}
#[deprecated = "Struct has moved to `frame_support::dispatch`"]
pub type PerDispatchClass<T> = dispatch::PerDispatchClass<T>;
#[deprecated = "Struct has moved to `frame_support::dispatch`"]
pub type PostDispatchInfo = dispatch::PostDispatchInfo;
#[deprecated = "Trait has moved to `frame_support::dispatch`"]
pub trait WeighData<T>: dispatch::WeighData<T> {
	fn weigh_data(&self, target: T) -> Weight {
		<Self as dispatch::WeighData<T>>::weigh_data(self, target)
	}
}
#[deprecated = "Trait has moved to `frame_support::dispatch`"]
pub trait WithPostDispatchInfo: dispatch::WithPostDispatchInfo {
	fn with_weight(self, actual_weight: Weight) -> dispatch::DispatchErrorWithPostInfo
	where
		Self: Sized,
	{
		<Self as dispatch::WithPostDispatchInfo>::with_weight(self, actual_weight)
	}
}
