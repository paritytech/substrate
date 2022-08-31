// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use criterion::{criterion_group, criterion_main, Criterion};

use futures::{future::{ready, Ready}, executor::block_on};
use sc_transaction_graph::*;
use codec::Encode;
use substrate_test_runtime::{Block, Extrinsic, Transfer, H256, AccountId};
use sp_runtime::{
	generic::BlockId,
	transaction_validity::{
		ValidTransaction, InvalidTransaction, TransactionValidity, TransactionTag as Tag,
		TransactionSource,
	},
};
use sp_core::blake2_256;

#[derive(Clone, Debug, Default)]
struct TestApi {
	nonce_dependant: bool,
}

impl TestApi {
	fn new_dependant() -> Self {
		TestApi { nonce_dependant: true }
	}
}

fn to_tag(nonce: u64, from: AccountId) -> Tag {
	let mut data = [0u8; 40];
	data[..8].copy_from_slice(&nonce.to_le_bytes()[..]);
	data[8..].copy_from_slice(&from.0[..]);
	data.to_vec()
}

impl ChainApi for TestApi {
	type Block = Block;
	type Error = sp_transaction_pool::error::Error;
	type ValidationFuture = Ready<sp_transaction_pool::error::Result<TransactionValidity>>;
	type BodyFuture = Ready<sp_transaction_pool::error::Result<Option<Vec<Extrinsic>>>>;

	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		_source: TransactionSource,
		uxt: ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {
		let nonce = uxt.transfer().nonce;
		let from = uxt.transfer().from.clone();

		match self.block_id_to_number(at) {
			Ok(Some(num)) if num > 5 => {
				return ready(
					Ok(Err(InvalidTransaction::Stale.into()))
				)
			},
			_ => {},
		}

		ready(
			Ok(Ok(ValidTransaction {
				priority: 4,
				requires: if nonce > 1 && self.nonce_dependant {
					vec![to_tag(nonce-1, from.clone())]
				} else { vec![] },
				provides: vec![to_tag(nonce, from)],
				longevity: 10,
				propagate: true,
			}))
		)
	}

	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<NumberFor<Self>>, Self::Error> {
		Ok(match at {
			BlockId::Number(num) => Some(*num),
			BlockId::Hash(_) => None,
		})
	}

	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<BlockHash<Self>>, Self::Error> {
		Ok(match at {
			BlockId::Number(num) => Some(H256::from_low_u64_be(*num)).into(),
			BlockId::Hash(_) => None,
		})
	}

	fn hash_and_length(&self, uxt: &ExtrinsicFor<Self>) -> (H256, usize) {
		let encoded = uxt.encode();
		(blake2_256(&encoded).into(), encoded.len())
	}

	fn block_body(&self, _id: &BlockId<Self::Block>) -> Self::BodyFuture {
		ready(Ok(None))
	}
}

fn uxt(transfer: Transfer) -> Extrinsic {
	Extrinsic::Transfer {
		transfer,
		signature: Default::default(),
		exhaust_resources_when_not_first: false,
	}
}

fn bench_configured(pool: Pool<TestApi>, number: u64) {
	let source = TransactionSource::External;
	let mut futures = Vec::new();
	let mut tags = Vec::new();

	for nonce in 1..=number {
		let xt = uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce,
		});

		tags.push(to_tag(nonce, AccountId::from_h256(H256::from_low_u64_be(1))));
		futures.push(pool.submit_one(&BlockId::Number(1), source, xt));
	}

	let res = block_on(futures::future::join_all(futures.into_iter()));
	assert!(res.iter().all(Result::is_ok));

	assert_eq!(pool.validated_pool().status().future, 0);
	assert_eq!(pool.validated_pool().status().ready, number as usize);

	// Prune all transactions.
	let block_num = 6;
	block_on(pool.prune_tags(
		&BlockId::Number(block_num),
		tags,
		vec![],
	)).expect("Prune failed");

	// pool is empty
	assert_eq!(pool.validated_pool().status().ready, 0);
	assert_eq!(pool.validated_pool().status().future, 0);
}

fn benchmark_main(c: &mut Criterion) {

	c.bench_function("sequential 50 tx", |b| {
		b.iter(|| {
			bench_configured(
				Pool::new(Default::default(), true.into(), TestApi::new_dependant().into()),
				50,
			);
		});
	});

	c.bench_function("random 100 tx", |b| {
		b.iter(|| {
			bench_configured(
				Pool::new(Default::default(), true.into(), TestApi::default().into()),
				100,
			);
		});
	});
}

criterion_group!(benches, benchmark_main);
criterion_main!(benches);
