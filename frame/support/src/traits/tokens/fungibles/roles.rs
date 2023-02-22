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

//! Inspect traits for Asset roles

pub trait Inspect<AccountId>: super::Inspect<AccountId> {
	// Get owner for an AssetId.
	fn owner(asset: Self::AssetId) -> Option<AccountId>;
	// Get issuer for an AssetId.
	fn issuer(asset: Self::AssetId) -> Option<AccountId>;
	// Get admin for an AssetId.
	fn admin(asset: Self::AssetId) -> Option<AccountId>;
	// Get freezer for an AssetId.
	fn freezer(asset: Self::AssetId) -> Option<AccountId>;
}
