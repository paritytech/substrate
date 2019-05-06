// Copyright 2018-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

/// Integrate grandpa finality with substrate service

use client;
use service::{FullBackend, FullExecutor, ServiceFactory};

pub type BlockImportForService<F> = crate::GrandpaBlockImport<
	FullBackend<F>,
	FullExecutor<F>,
	<F as ServiceFactory>::Block,
	<F as ServiceFactory>::RuntimeApi,
	client::Client<
        FullBackend<F>,
        FullExecutor<F>,
        <F as ServiceFactory>::Block,
        <F as ServiceFactory>::RuntimeApi
    >,
	<F as ServiceFactory>::SelectChain
>;

pub type LinkHalfForService<F> = crate::LinkHalf<
	FullBackend<F>,
	FullExecutor<F>,
	<F as ServiceFactory>::Block,
	<F as ServiceFactory>::RuntimeApi,
	<F as ServiceFactory>::SelectChain
>;
