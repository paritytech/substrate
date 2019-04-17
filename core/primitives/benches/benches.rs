// Copyright 2019 Parity Technologies
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

#![feature(test)]

extern crate test;
use hex_literal::{hex, hex_impl};
use substrate_primitives::hashing::{twox_128, blake2_128};

const RANDOM: [u8; 968] = hex!("a494a9df75845413c3b2732f1e54c5ace3474a77ed311d08cdb491b60408901d0ca7485d72a64d47bae1c4c3a91403650283c7432347f5c068cc1b07d843c2275bf8d8d11f9ca7a6d32c99e5b0b21d057a8ceaecc075afc2a34a82d3a36f8efb99a8e8c244db1e7e0d7f5d72bca68f209f04eef2aad9f04f772effc532f9e84fc8c663880cef8021f7926a0900e6d636ac5f57de8007ccb8d2fa348a27c7211f07fae5ef275c1ab54eacafde539079b2d106f254ab242a7e530460e7ed99d9771746ce2f5a08f68833a9109b0f57764964d66fee6616a5fef8a9de13701c470d1f3511c3960c7d92bc3e0e2a56833f0ec0354f7d0360960c87bdf0adfea9bf167917b221de806bf9279870f2adc2f9117ffd584a3e065905ed9d7e327e5fa3ca8a1f7e9947026b0db868ab7138a355daf67b742c0aa1eea22e94c865608babe2677880179e6bd990713d1e7a2421fe38e66983918d4a1028530fa24cbb372b9f207a7611f5cf0e0f73c859d85751d7324bb73fa23d8899531a9cb05eb367a65773622947b6fe228c78a34b612748e9717bcb3bc1c0354ca89dfd15a544f8076ad9f48ca36f259b0fbbc891f34095de03baaa93f7d84685a15383b658d62c854808031218c15dd9a2b8f7db070912c9f7b1e8b20bb282a84d338b04cf94c8283e04ddf156c5795acbe829e3944184a77e711d62bf8f1d5a0ed1b5adf85fbd91dee6f7f977271c0949d018858e94c7dd5380a8337fa3936e4a4286c6b7c7c4103d590e369f12bec1621f94a2c80726247b6911bd9b8c65d5039b2e96098e5b52b4d7ab636f39115292314e0afb38ce17a69e93838a69ce23d684065f25fda0e601f3ee56431effed7b118a80dea0bccdecd8775e9ff96bcd31a7a805317c3650ea4c4a1df6adbe184e762a24bc9359eac4e81b2253b9a3dd5086974506ad6655b0be3b903837c2c73844239f19b9ba6fe1ac1b9f9c78c1cca223a5affd21a2442bef064c14c2b8ff88cd65e8bc7432b61516f3250803636e31028a62f540966aa1471eee46cc95d3590f272d7eb2ab8273ad0f4442cf197e759498445bb60bf87f394142ede5796f0f9353a8ddb34e9b6edd4c82149b65b6d3480ad3af534cd2e5646a12de6a1500a20613f2cf23a81ace0abd3d25a767522cb79e301342f564aaebd567723e5df0cfd4973fcb6b8ed66fe543abf969c22685ffc504068c347dc28c2f1bf62710cc9ed11386906b69bded1e6a8232d4f9980db3e1eca8268ba420cd5b9fb69bdb090562af0167bac782e954909a5a84f53cb067aaadbf5635ebc1b7d9304aee0407c2d14f1ea95d132483a335435b090cf0e1a7d3e2ba3adc40d21042119ed005df10");

const MAX_KEY_SIZE: u32 = 32;

fn data_set() -> Vec<Vec<u8>> {
	let mut rnd = RANDOM.iter().cycle();
	let mut res = Vec::new();
	for size in 1..=MAX_KEY_SIZE {
		for _ in 0..1_000 {
			let value = (0..size)
				.map(|_| rnd.next().unwrap().clone())
				.collect();
			res.push(value);
		}
	}
	res
}

fn bench_hash_128(b: &mut test::Bencher, f: &Fn(&[u8]) -> [u8; 16]) {
	let data_set = data_set();
	b.iter(|| {
		for data in &data_set {
			let _a = f(data);
		}
	});
}

#[bench]
fn bench_blake2_128(b: &mut test::Bencher) {
	bench_hash_128(b, &blake2_128);
}

#[bench]
fn bench_twox_128(b: &mut test::Bencher) {
	bench_hash_128(b, &twox_128);
}
