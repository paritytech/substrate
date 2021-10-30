// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use crate::{Error, InherentData, InherentIdentifier};
use sp_runtime::traits::Block as BlockT;

/// Something that can create inherent data providers.
///
/// It is possible for the caller to provide custom arguments to the callee by setting the
/// `ExtraArgs` generic parameter.
///
/// The crate already provides some convience implementations of this trait for
/// `Box<dyn CreateInherentDataProviders>` and closures. So, it should not be required to implement
/// this trait manually.
#[async_trait::async_trait]
pub trait CreateInherentDataProviders<Block: BlockT, ExtraArgs>: Send + Sync {
	/// The inherent data providers that will be created.
	type InherentDataProviders: InherentDataProvider;

	/// Create the inherent data providers at the given `parent` block using the given `extra_args`.
	async fn create_inherent_data_providers(
		&self,
		parent: Block::Hash,
		extra_args: ExtraArgs,
	) -> Result<Self::InherentDataProviders, Box<dyn std::error::Error + Send + Sync>>;
}

#[async_trait::async_trait]
impl<F, Block, IDP, ExtraArgs, Fut> CreateInherentDataProviders<Block, ExtraArgs> for F
where
	Block: BlockT,
	F: Fn(Block::Hash, ExtraArgs) -> Fut + Sync + Send,
	Fut: std::future::Future<Output = Result<IDP, Box<dyn std::error::Error + Send + Sync>>>
		+ Send
		+ 'static,
	IDP: InherentDataProvider + 'static,
	ExtraArgs: Send + 'static,
{
	type InherentDataProviders = IDP;

	async fn create_inherent_data_providers(
		&self,
		parent: Block::Hash,
		extra_args: ExtraArgs,
	) -> Result<Self::InherentDataProviders, Box<dyn std::error::Error + Send + Sync>> {
		(*self)(parent, extra_args).await
	}
}

#[async_trait::async_trait]
impl<Block: BlockT, ExtraArgs: Send, IDPS: InherentDataProvider>
	CreateInherentDataProviders<Block, ExtraArgs>
	for Box<dyn CreateInherentDataProviders<Block, ExtraArgs, InherentDataProviders = IDPS>>
{
	type InherentDataProviders = IDPS;

	async fn create_inherent_data_providers(
		&self,
		parent: Block::Hash,
		extra_args: ExtraArgs,
	) -> Result<Self::InherentDataProviders, Box<dyn std::error::Error + Send + Sync>> {
		(**self).create_inherent_data_providers(parent, extra_args).await
	}
}

/// Something that provides inherent data.
#[async_trait::async_trait]
pub trait InherentDataProvider: Send + Sync {
	/// Convenience function for creating [`InherentData`].
	///
	/// Basically maps around [`Self::provide_inherent_data`].
	fn create_inherent_data(&self) -> Result<InherentData, Error> {
		let mut inherent_data = InherentData::new();
		self.provide_inherent_data(&mut inherent_data)?;
		Ok(inherent_data)
	}

	/// Provide inherent data that should be included in a block.
	///
	/// The data should be stored in the given `InherentData` structure.
	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), Error>;

	/// Convert the given encoded error to a string.
	///
	/// If the given error could not be decoded, `None` should be returned.
	async fn try_handle_error(
		&self,
		identifier: &InherentIdentifier,
		error: &[u8],
	) -> Option<Result<(), Error>>;
}

#[impl_trait_for_tuples::impl_for_tuples(30)]
#[async_trait::async_trait]
impl InherentDataProvider for Tuple {
	for_tuples!( where #( Tuple: Send + Sync )* );
	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), Error> {
		for_tuples!( #( Tuple.provide_inherent_data(inherent_data)?; )* );
		Ok(())
	}

	async fn try_handle_error(
		&self,
		identifier: &InherentIdentifier,
		error: &[u8],
	) -> Option<Result<(), Error>> {
		for_tuples!( #(
			if let Some(r) = Tuple.try_handle_error(identifier, error).await { return Some(r) }
		)* );

		None
	}
}
