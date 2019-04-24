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
use criterion::{Criterion, criterion_group, criterion_main};
criterion_group!(benches, benchmark);
criterion_main!(benches);

fn benchmark(c: &mut Criterion) {
	trie_bench::standard_benchmark::<
		substrate_primitives::Blake2Hasher,
		substrate_trie::NodeCodec<substrate_primitives::Blake2Hasher>,
		substrate_trie::TrieStream,
	>(c, "substrate-blake2");
	trie_bench::standard_benchmark::<
		keccak_hasher::KeccakHasher,
		substrate_trie::NodeCodec<keccak_hasher::KeccakHasher>,
		substrate_trie::TrieStream,
	>(c, "substrate-keccak");
}
