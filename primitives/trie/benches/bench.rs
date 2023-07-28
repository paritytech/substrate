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

use criterion::{criterion_group, criterion_main, Criterion};
criterion_group!(benches, benchmark);
criterion_main!(benches);

fn benchmark(c: &mut Criterion) {
	trie_bench::standard_benchmark::<
		sp_trie::LayoutV1<sp_runtime::traits::BlakeTwo256>,
		sp_trie::TrieStream,
	>(c, "substrate-blake2");
	trie_bench::standard_benchmark::<
		sp_trie::LayoutV1<sp_runtime::traits::BlakeTwo256>,
		sp_trie::TrieStream,
	>(c, "substrate-keccak");
}
