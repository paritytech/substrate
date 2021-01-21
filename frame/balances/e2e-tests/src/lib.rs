use substrate_test_runner::{Node, ChainInfo};
use pallet_balances::Call as BalancesCall;
use sp_runtime::{MultiAddress, MultiSignature};
use sp_runtime::AccountId32;
use sp_runtime::traits::Block as BlockT;
use sp_runtime::generic::UncheckedExtrinsic;
use codec::Encode;
use frame_support::traits::Get;

type Extrinsic<R, S> = UncheckedExtrinsic<
    MultiAddress<<R as frame_system::Config>::AccountId, <R as frame_system::Config>::Index>,
    <R as frame_system::Config>::Call,
    MultiSignature,
    S,
>;

/// Tests the Balances::force_transfer call
pub fn force_transfer<T>(
    node: &Node<T>,
    account1: <T::Runtime as frame_system::Config>::AccountId,
    account2: <T::Runtime as frame_system::Config>::AccountId,
)
    where
        T: ChainInfo,
        T::Runtime: pallet_balances::Config,
        <T::Runtime as frame_system::Config>::Call: From<BalancesCall<T::Runtime>> + Encode,
        <T::Runtime as pallet_balances::Config>::Balance: From<u8>,
        <T::Runtime as frame_system::Config>::AccountId: From<AccountId32> + Encode,
        <T::Block as BlockT>::Extrinsic: From<Extrinsic<T::Runtime, T::SignedExtras>>,
        <<T::Runtime as frame_system::Config>::Lookup as sp_runtime::traits::StaticLookup>::Source:
            From<<T::Runtime as frame_system::Config>::AccountId>,
        AccountId32: std::borrow::Borrow<<T::Runtime as frame_system::Config>::AccountId>,
{
    type Balances<T> = pallet_balances::Module<T>;

    let (account1_balance, account2_balance) = node.with_state(|| (
        Balances::<T::Runtime>::free_balance(account1.clone()),
        Balances::<T::Runtime>::free_balance(account2.clone()),
    ));
    let balance = account1_balance / 2u8.into();

    let call = BalancesCall::force_transfer(account1.clone().into(), account2.clone().into(), balance.into());
    T::dispatch_with_root(call.into(), &node);

    let new_account2_balance = node.with_state(|| Balances::<T::Runtime>::free_balance(account2.clone()));

    assert_eq!(new_account2_balance, account2_balance + balance);
    node.clean();
}

/// Tests the Balances::set_balance call
pub fn set_balance<T>(
    node: &Node<T>,
    account1: <T::Runtime as frame_system::Config>::AccountId,
)
    where
        T: ChainInfo,
        T::Runtime: pallet_balances::Config,
        <T::Runtime as frame_system::Config>::Call: From<BalancesCall<T::Runtime>> + Encode,
        <T::Runtime as pallet_balances::Config>::Balance: From<u128>,
        <T::Runtime as frame_system::Config>::AccountId: From<AccountId32> + Encode,
        <T::Block as BlockT>::Extrinsic: From<Extrinsic<T::Runtime, T::SignedExtras>>,
        <<T::Runtime as frame_system::Config>::Lookup as sp_runtime::traits::StaticLookup>::Source:
            From<<T::Runtime as frame_system::Config>::AccountId>,
        AccountId32: std::borrow::Borrow<<T::Runtime as frame_system::Config>::AccountId>,
{
    type Balances<T> = pallet_balances::Module<T>;

    let account1_balance = node.with_state(|| (
        Balances::<T::Runtime>::free_balance(account1.clone())
    ));

    let new_balance = account1_balance * 2.into();

    let call = BalancesCall::set_balance(account1.clone().into(), new_balance, 0u8.into());
    T::dispatch_with_root(call.into(), &node);

    let updated_account1_balance = node.with_state(|| Balances::<T::Runtime>::free_balance(account1.clone()));

    assert_eq!(updated_account1_balance, new_balance);
    node.clean();
}

/// Tests the Balances::transfer_keep_alive call
pub fn transfer_keep_alive<T>(
    node: &Node<T>,
    account1: <T::Runtime as frame_system::Config>::AccountId,
    account2: <T::Runtime as frame_system::Config>::AccountId,
)
    where
        T: ChainInfo,
        T::Runtime: pallet_balances::Config,
        <T::Runtime as frame_system::Config>::Call: From<BalancesCall<T::Runtime>> + Encode,
        <T::Runtime as pallet_balances::Config>::Balance: From<u8>,
        <T::Runtime as frame_system::Config>::AccountId: From<AccountId32> + Encode,
        <T::Block as BlockT>::Extrinsic: From<Extrinsic<T::Runtime, T::SignedExtras>>,
        <<T::Runtime as frame_system::Config>::Lookup as sp_runtime::traits::StaticLookup>::Source:
            From<<T::Runtime as frame_system::Config>::AccountId>,
        AccountId32: std::borrow::Borrow<<T::Runtime as frame_system::Config>::AccountId>,
{
    type Balances<T> = pallet_balances::Module<T>;

    let (account2_balance, account1_balance) = node.with_state(|| (
        Balances::<T::Runtime>::free_balance(account2.clone()),
        Balances::<T::Runtime>::free_balance(account1.clone())
    ));
    // attempt to send more than the existential deposit
    let balance = account2_balance - (<T::Runtime as pallet_balances::Config>::ExistentialDeposit::get() / 2u8.into());

    let call = BalancesCall::transfer_keep_alive(account1.clone().into(), balance.into());
    node.submit_extrinsic(call, account2.clone());
    node.seal_blocks(1);

    // assert that the transaction failed to dispatch
    node.assert_log_line("LiquidityRestrictions");

    let new_balance = node.with_state(|| Balances::<T::Runtime>::free_balance(account1.clone()));

    assert_eq!(account1_balance, new_balance);
    node.clean();
}
