use criterion::{criterion_group, criterion_main, Criterion};

use futures::executor::block_on;
use substrate_transaction_graph::*;
use sr_primitives::transaction_validity::ValidTransaction;
use codec::Encode;
use test_runtime::{Block, Extrinsic, Transfer, H256, AccountId};
use sr_primitives::{
	generic::BlockId,
	transaction_validity::{TransactionValidity, TransactionTag as Tag},
};
use primitives::blake2_256;

#[derive(Clone, Debug, Default)]
struct TestApi {
	nonce_limit: Option<u64>,
}

impl TestApi {
	fn new_with_limit(limit: u64) -> Self {
		TestApi { nonce_limit: Some(limit) }
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
	type Hash = H256;
	type Error = error::Error;
	type ValidationFuture = futures::future::Ready<error::Result<TransactionValidity>>;

	fn validate_transaction(
		&self,
		_at: &BlockId<Self::Block>,
		uxt: ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {
		let nonce = uxt.transfer().nonce;
		let from = uxt.transfer().from.clone();

		let mut requires = vec![];
		if nonce > 1 && self.nonce_limit.is_some() {
			requires.push(to_tag(nonce-1, from.clone()));
		};

		let mut provides = vec![];
		provides.push(to_tag(nonce, from.clone()));
		if self.nonce_limit.is_some() {
			provides.push(to_tag(nonce+1, from.clone()));
		}

		futures::future::ready(
			Ok(Ok(ValidTransaction {
				priority: 4,
				requires,
				provides,
				longevity: 10,
				propagate: true,
			}))
		)
	}

	fn block_id_to_number(&self, at: &BlockId<Self::Block>) -> Result<Option<NumberFor<Self>>, Self::Error> {
		Ok(match at {
			BlockId::Number(num) => Some(*num),
			BlockId::Hash(_) => None,
		})
	}

	fn block_id_to_hash(&self, at: &BlockId<Self::Block>) -> Result<Option<BlockHash<Self>>, Self::Error> {
		Ok(match at {
			BlockId::Number(num) => Some(H256::from_low_u64_be(*num)).into(),
			BlockId::Hash(_) => None,
		})
	}

	fn hash_and_length(&self, uxt: &ExtrinsicFor<Self>) -> (Self::Hash, usize) {
		let encoded = uxt.encode();
		(blake2_256(&encoded).into(), encoded.len())
	}
}

fn uxt(transfer: Transfer) -> Extrinsic {
	Extrinsic::Transfer(transfer, Default::default())
}

fn bench_configured(pool: Pool<TestApi>, number: u64) {
	let mut nonce = 1;
	let mut futures = Vec::new();

	for _ in 0..number {
		let xt = uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce,
		});

		nonce += 1;

		futures.push(pool.submit_one(&BlockId::Number(1), xt));
	}

	let _res = block_on(futures::future::join_all(futures.into_iter()));

	// instantly producing "blocks" and pruning all ready until no ready
	let mut block_num = 2;
	loop {
		if let Some(ready) = pool.ready().next() {
			//dbg!(ready.clone());
			block_on(pool.prune_tags(
				&BlockId::Number(block_num),
				vec![to_tag(ready.data.transfer().nonce, ready.data.transfer().from.clone())],
				vec![ready.hash],
			)).expect("Prune failed");
		} else {
			break;
		}

		block_num += 1;

	}

	// pool is empty
	assert_eq!(pool.status().ready, 0);
	assert_eq!(pool.status().future, 0);
}

fn benchmark_main(c: &mut Criterion) {

    c.bench_function("sequental 50 tx", |b| {
		b.iter(|| {
			bench_configured(Pool::new(Default::default(), TestApi::new_with_limit(50)), 50);
		});
	});

	c.bench_function("random 100 tx", |b| {
		b.iter(|| {
			bench_configured(Pool::new(Default::default(), TestApi::default()), 100);
		});
	});
}

criterion_group!(benches, benchmark_main);
criterion_main!(benches);
