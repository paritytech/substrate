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

//! Test crate for frame_support. Allow to make use of `frame_support::decl_storage`.
//! See tests directory.

// Make sure we fail compilation on warnings
#![warn(missing_docs)]
#![deny(warnings)]

#[cfg(test)]
mod pallet_version;

/// The configuration trait
pub trait Config: 'static {
	/// The runtime origin type.
	type Origin: codec::Codec + codec::EncodeLike + Default;
	/// The block number type.
	type BlockNumber: codec::Codec + codec::EncodeLike + Default;
	/// The information about the pallet setup in the runtime.
	type PalletInfo: frame_support::traits::PalletInfo;
	/// The db weights.
	type DbWeight: frame_support::traits::Get<frame_support::weights::RuntimeDbWeight>;
}

frame_support::decl_module! {
	/// Some test module
	pub struct Module<T: Config> for enum Call where origin: T::Origin, system=self {}
}
