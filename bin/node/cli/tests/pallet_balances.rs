mod runtime;
use runtime::NodeTemplateChainInfo;
use substrate_test_runner::Node;
use pallet_balances::tests_e2e;

#[test]
fn test_pallet_balances() {
    let node = Node::<NodeTemplateChainInfo>::new().unwrap();
    tests_e2e::force_transfer(&node);
    tests_e2e::set_balance(&node);
    tests_e2e::transfer_keep_alive(&node);
}
