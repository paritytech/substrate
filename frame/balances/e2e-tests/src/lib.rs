use substrate_test_runner::{Node, ChainInfo};
use pallet_sudo::Call as SudoCall;
use pallet_balances::Call as BalancesCall;
use sp_keyring::sr25519::Keyring::{Alice, Bob};
use sp_runtime::{traits::IdentifyAccount, MultiSigner, MultiAddress, MultiSignature};
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

pub fn force_transfer<T>(node: &Node<T>)
    where
        T: ChainInfo,
        T::Runtime: pallet_sudo::Config + pallet_balances::Config,
        <T::Runtime as frame_system::Config>::Call: From<SudoCall<T::Runtime>> + From<BalancesCall<T::Runtime>> + Encode,
        <T::Runtime as pallet_sudo::Config>::Call: From<BalancesCall<T::Runtime>>,
        <T::Runtime as pallet_balances::Config>::Balance: From<u128>,
        <T::Runtime as frame_system::Config>::AccountId: From<AccountId32> + Encode,
        <T::Block as BlockT>::Extrinsic: From<Extrinsic<T::Runtime, T::SignedExtras>>,
        <<T::Runtime as frame_system::Config>::Lookup as sp_runtime::traits::StaticLookup>::Source: From<AccountId32>,
        AccountId32: std::borrow::Borrow<<T::Runtime as frame_system::Config>::AccountId>
{
    type Balances<T> = pallet_balances::Module<T>;
    let (alice, bob) = (
        MultiSigner::from(Alice.public()).into_account(),
        MultiSigner::from(Bob.public()).into_account(),
    );
    let (alice_balance, bob_balance) = node.with_state(|| (
        Balances::<T::Runtime>::free_balance(alice.clone()),
        Balances::<T::Runtime>::free_balance(bob.clone()),
    ));
    let balance = alice_balance / 2u128.into();

    let balances_call = BalancesCall::force_transfer(alice.clone().into(), bob.clone().into(), balance.into());
    node.submit_extrinsic(
        SudoCall::sudo(Box::new(balances_call.into())),
        alice.into()
    );
    node.seal_blocks(1);

    // TODO: figure out events
    // let events = node.events()
    //     .into_iter()
    //     .filter(|event| {
    //         match &event.event {
    //             Event::pallet_balances(RawEvent::Transfer(_, _, _)) => true,
    //             _ => false,
    //         }
    //     })
    //     .collect::<Vec<_>>();
    // assert_eq!(events.len(), 1);

    let new_bob_balance = node.with_state(|| Balances::<T::Runtime>::free_balance(bob.clone()));

    assert_eq!(new_bob_balance, bob_balance + (balance))
}

pub fn set_balance<T>(node: &Node<T>)
    where
        T: ChainInfo,
        T::Runtime: pallet_sudo::Config + pallet_balances::Config,
        <T::Runtime as frame_system::Config>::Call: From<SudoCall<T::Runtime>> + From<BalancesCall<T::Runtime>> + Encode,
        <T::Runtime as pallet_sudo::Config>::Call: From<BalancesCall<T::Runtime>>,
        <T::Runtime as pallet_balances::Config>::Balance: From<u128>,
        <T::Runtime as frame_system::Config>::AccountId: From<AccountId32> + Encode,
        <T::Block as BlockT>::Extrinsic: From<Extrinsic<T::Runtime, T::SignedExtras>>,
        <<T::Runtime as frame_system::Config>::Lookup as sp_runtime::traits::StaticLookup>::Source: From<AccountId32>,
        AccountId32: std::borrow::Borrow<<T::Runtime as frame_system::Config>::AccountId>,
{
    type Balances<T> = pallet_balances::Module<T>;
    let (alice, bob) = (
        MultiSigner::from(Alice.public()).into_account(),
        MultiSigner::from(Bob.public()).into_account(),
    );
    let (alice_balance, _bob_balance) = node.with_state(|| (
        Balances::<T::Runtime>::free_balance(alice.clone()),
        Balances::<T::Runtime>::free_balance(alice.clone())
    ));

    let call = BalancesCall::set_balance(bob.clone().into(), alice_balance, 0u128.into());
    node.submit_extrinsic(
        SudoCall::sudo(Box::new(call.into())),
        alice.into()
    );
    node.seal_blocks(1);

    // let events = node.events()
    //     .into_iter()
    //     .filter(|event| {
    //         match &event.event {
    //             Event::pallet_balances(RawEvent::BalanceSet(_, _, _)) => true,
    //             _ => false,
    //         }
    //     })
    //     .collect::<Vec<_>>();
    // assert_eq!(events.len(), 1);

    let updated_bob_balance = node.with_state(|| Balances::<T::Runtime>::free_balance(bob.clone()));

    assert_eq!(updated_bob_balance, alice_balance)
}

pub fn transfer_keep_alive<T>(node: &Node<T>)
    where
        T: ChainInfo,
        T::Runtime: pallet_sudo::Config + pallet_balances::Config,
        <T::Runtime as frame_system::Config>::Call: From<SudoCall<T::Runtime>> + From<BalancesCall<T::Runtime>> + Encode,
        <T::Runtime as pallet_sudo::Config>::Call: From<BalancesCall<T::Runtime>>,
        <T::Runtime as pallet_balances::Config>::Balance: From<u128>,
        <T::Runtime as frame_system::Config>::AccountId: From<AccountId32> + Encode,
        <T::Block as BlockT>::Extrinsic: From<Extrinsic<T::Runtime, T::SignedExtras>>,
        <<T::Runtime as frame_system::Config>::Lookup as sp_runtime::traits::StaticLookup>::Source: From<AccountId32>,
        AccountId32: std::borrow::Borrow<<T::Runtime as frame_system::Config>::AccountId>,
{
    type Balances<T> = pallet_balances::Module<T>;
    let (alice, bob) = (
        MultiSigner::from(Alice.public()).into_account(),
        MultiSigner::from(Bob.public()).into_account(),
    );
    let (bob_balance, alice_balance) = node.with_state(|| (
        Balances::<T::Runtime>::free_balance(bob.clone()),
        Balances::<T::Runtime>::free_balance(alice.clone())
    ));
    // attempt to send more than the existential deposit
    let balance = bob_balance - (<T::Runtime as pallet_balances::Config>::ExistentialDeposit::get() / 2u128.into());

    let call = BalancesCall::transfer_keep_alive(alice.clone().into(), balance.into());
    node.submit_extrinsic(call, bob.clone().into());
    node.seal_blocks(1);

    // assert that the transaction failed to dispatch
    node.assert_log_line("LiquidityRestrictions");

    let new_balance = node.with_state(|| Balances::<T::Runtime>::free_balance(alice.clone()));

    assert_eq!(alice_balance, new_balance)
}
