use sc_transaction_pool::test_helpers::{Pool, RevalidationQueue};
use sc_transaction_pool_api::TransactionSource;
use substrate_test_runtime_transaction_pool::{TestApi, uxt};
use futures::executor::block_on;
use substrate_test_runtime_client::AccountKeyring::*;
use std::sync::Arc;
use sp_runtime::generic::BlockId;

fn setup() -> (Arc<TestApi>, Pool<TestApi>) {
    let test_api = Arc::new(TestApi::empty());
    let pool = Pool::new(Default::default(), true.into(), test_api.clone());
    (test_api, pool)
}

#[test]
fn smoky() {
    let (api, pool) = setup();
    let pool = Arc::new(pool);
    let queue = Arc::new(RevalidationQueue::new(api.clone(), pool.clone()));

    let uxt = uxt(Alice, 0);
    let uxt_hash = block_on(
        pool.submit_one(&BlockId::number(0), TransactionSource::External, uxt.clone())
    ).expect("Should be valid");

    block_on(queue.revalidate_later(0, vec![uxt_hash]));

    // revalidated in sync offload 2nd time
    assert_eq!(api.validation_requests().len(), 2);
    // number of ready
    assert_eq!(pool.validated_pool().status().ready, 1);
}