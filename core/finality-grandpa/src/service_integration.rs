// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
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
>;

pub type LinkHalfForService<F> = crate::LinkHalf<
	FullBackend<F>,
	FullExecutor<F>,
	<F as ServiceFactory>::Block,
	<F as ServiceFactory>::RuntimeApi
>;
