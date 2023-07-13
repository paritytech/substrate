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

use frame_support::{
	metadata_ir::{
		RuntimeApiMetadataIR, RuntimeApiMethodMetadataIR, RuntimeApiMethodParamMetadataIR,
	},
	traits::ConstU32,
};
use scale_info::{form::MetaForm, meta_type};
use sp_runtime::traits::Block as BlockT;

pub type BlockNumber = u64;
pub type Index = u64;
pub type Header = sp_runtime::generic::Header<u32, sp_runtime::traits::BlakeTwo256>;
pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, RuntimeCall, (), ()>;

impl frame_system::Config for Runtime {
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type BaseCallFilter = frame_support::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type RuntimeCall = RuntimeCall;
	type Hash = sp_runtime::testing::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Block = Block;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU32<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

frame_support::construct_runtime!(
	pub enum Runtime
	{
		System: frame_system,
	}
);

sp_api::decl_runtime_apis! {
	/// ApiWithCustomVersion trait documentation
	///
	/// Documentation on multiline.
	pub trait Api {
		fn test(data: u64);
		/// something_with_block.
		fn something_with_block(block: Block) -> Block;
		fn function_with_two_args(data: u64, block: Block);
		fn same_name();
		fn wild_card(_: u32);
	}
}

sp_api::impl_runtime_apis! {
	impl self::Api<Block> for Runtime {
		fn test(_data: u64) {
			unimplemented!()
		}

		fn something_with_block(_: Block) -> Block {
			unimplemented!()
		}

		fn function_with_two_args(_: u64, _: Block) {
			unimplemented!()
		}

		fn same_name() {}

		fn wild_card(_: u32) {}
	}

	impl sp_api::Core<Block> for Runtime {
		fn version() -> sp_version::RuntimeVersion {
			unimplemented!()
		}
		fn execute_block(_: Block) {
			unimplemented!()
		}
		fn initialize_block(_: &<Block as BlockT>::Header) {
			unimplemented!()
		}
	}
}

#[test]
fn runtime_metadata() {
	fn maybe_docs(doc: Vec<&'static str>) -> Vec<&'static str> {
		if cfg!(feature = "no-metadata-docs") {
			vec![]
		} else {
			doc
		}
	}

	let expected_runtime_metadata = vec![
		RuntimeApiMetadataIR {
			name: "Api",
			methods: vec![
				RuntimeApiMethodMetadataIR {
					name: "test",
					inputs: vec![RuntimeApiMethodParamMetadataIR::<MetaForm> {
						name: "data",
						ty: meta_type::<u64>(),
					}],
					output: meta_type::<()>(),
					docs: vec![],
				},
				RuntimeApiMethodMetadataIR {
					name: "something_with_block",
					inputs: vec![RuntimeApiMethodParamMetadataIR::<MetaForm> {
						name: "block",
						ty: meta_type::<Block>(),
					}],
					output: meta_type::<Block>(),
					docs: maybe_docs(vec![" something_with_block."]),
				},
				RuntimeApiMethodMetadataIR {
					name: "function_with_two_args",
					inputs: vec![
						RuntimeApiMethodParamMetadataIR::<MetaForm> {
							name: "data",
							ty: meta_type::<u64>(),
						},
						RuntimeApiMethodParamMetadataIR::<MetaForm> {
							name: "block",
							ty: meta_type::<Block>(),
						},
					],
					output: meta_type::<()>(),
					docs: vec![],
				},
				RuntimeApiMethodMetadataIR {
					name: "same_name",
					inputs: vec![],
					output: meta_type::<()>(),
					docs: vec![],
				},
				RuntimeApiMethodMetadataIR {
					name: "wild_card",
					inputs: vec![RuntimeApiMethodParamMetadataIR::<MetaForm> {
						name: "_",
						ty: meta_type::<u32>(),
					}],
					output: meta_type::<()>(),
					docs: vec![],
				},
			],
			docs: maybe_docs(vec![
				" ApiWithCustomVersion trait documentation",
				"",
				" Documentation on multiline.",
			]),
		},
		RuntimeApiMetadataIR {
			name: "Core",
			methods: vec![
				RuntimeApiMethodMetadataIR {
					name: "version",
					inputs: vec![],
					output: meta_type::<sp_version::RuntimeVersion>(),
					docs: maybe_docs(vec![" Returns the version of the runtime."]),
				},
				RuntimeApiMethodMetadataIR {
					name: "execute_block",
					inputs: vec![RuntimeApiMethodParamMetadataIR::<MetaForm> {
						name: "block",
						ty: meta_type::<Block>(),
					}],
					output: meta_type::<()>(),
					docs: maybe_docs(vec![" Execute the given block."]),
				},
				RuntimeApiMethodMetadataIR {
					name: "initialize_block",
					inputs: vec![RuntimeApiMethodParamMetadataIR::<MetaForm> {
						name: "header",
						ty: meta_type::<&<Block as BlockT>::Header>(),
					}],
					output: meta_type::<()>(),
					docs: maybe_docs(vec![" Initialize a block with the given header."]),
				},
			],
			docs: maybe_docs(vec![
				" The `Core` runtime api that every Substrate runtime needs to implement.",
			]),
		},
	];

	let rt = Runtime;
	let runtime_metadata = (&rt).runtime_metadata();
	pretty_assertions::assert_eq!(runtime_metadata, expected_runtime_metadata);
}
