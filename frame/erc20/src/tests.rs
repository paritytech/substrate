#![cfg(test)]

use super::mock::{
    assert_events, balances, event_exists, expect_event, new_test_ext, Balances, Bridge, Call,
    Erc721, Erc721Id, Event, Example, HashId, NativeTokenId, Origin, ProposalLifetime, Test,
    ENDOWED_BALANCE, RELAYER_A, RELAYER_B, RELAYER_C,
};
use super::*;
use frame_support::dispatch::DispatchError;
use frame_support::{assert_noop, assert_ok};

use codec::Encode;
use example_erc721::Erc721Token;
use sp_core::{blake2_256, H256};

const TEST_THRESHOLD: u32 = 2;

fn make_remark_proposal(hash: H256) -> Call {
    Call::Example(crate::Call::remark(hash))
}

fn make_transfer_proposal(to: u64, amount: u64) -> Call {
    Call::Example(crate::Call::transfer(to, amount.into()))
}

#[test]
fn transfer_hash() {
    new_test_ext().execute_with(|| {
        let dest_chain = 0;
        let resource_id = HashId::get();
        let hash: H256 = "ABC".using_encoded(blake2_256).into();

        assert_ok!(Bridge::set_threshold(Origin::root(), TEST_THRESHOLD,));

        assert_ok!(Bridge::whitelist_chain(Origin::root(), dest_chain.clone()));
        assert_ok!(Example::transfer_hash(
            Origin::signed(1),
            hash.clone(),
            dest_chain,
        ));

        expect_event(bridge::RawEvent::GenericTransfer(
            dest_chain,
            1,
            resource_id,
            hash.as_ref().to_vec(),
        ));
    })
}

/* #[test]
fn transfer_native() {
    new_test_ext().execute_with(|| {
        let dest_chain = 0;
        let resource_id = NativeTokenId::get();
        let amount: u64 = 100;
        let recipient = vec![99];

        assert_ok!(Bridge::whitelist_chain(Origin::root(), dest_chain.clone()));
        assert_ok!(Example::transfer_native(
            Origin::signed(RELAYER_A),
            amount.clone(),
            recipient.clone(),
            dest_chain,
        ));

        expect_event(bridge::RawEvent::FungibleTransfer(
            dest_chain,
            1,
            resource_id,
            amount.into(),
            recipient,
        ));
    })
} */

#[test]
fn transfer_erc721() {
    new_test_ext().execute_with(|| {
        let dest_chain = 0;
        let resource_id = Erc721Id::get();
        let token_id: U256 = U256::from(100);
        let token_id_slice: &mut [u8] = &mut [0; 32];
        token_id.to_big_endian(token_id_slice);
        let metadata: Vec<u8> = vec![1, 2, 3, 4];
        let recipient = vec![99];

        // Create a token
        assert_ok!(Erc721::mint(
            Origin::root(),
            RELAYER_A,
            token_id,
            metadata.clone()
        ));
        assert_eq!(
            Erc721::tokens(token_id).unwrap(),
            Erc721Token {
                id: token_id,
                metadata: metadata.clone()
            }
        );

        // Whitelist destination and transfer
        assert_ok!(Bridge::whitelist_chain(Origin::root(), dest_chain.clone()));
        assert_ok!(Example::transfer_erc721(
            Origin::signed(RELAYER_A),
            recipient.clone(),
            token_id,
            dest_chain,
        ));

        expect_event(bridge::RawEvent::NonFungibleTransfer(
            dest_chain,
            1,
            resource_id,
            token_id_slice.to_vec(),
            recipient.clone(),
            metadata,
        ));

        // Ensure token no longer exists
        assert_eq!(Erc721::tokens(token_id), None);

        // Transfer should fail as token doesn't exist
        assert_noop!(
            Example::transfer_erc721(
                Origin::signed(RELAYER_A),
                recipient.clone(),
                token_id,
                dest_chain,
            ),
            Error::<Test>::InvalidTransfer
        );
    })
}

#[test]
fn execute_remark() {
    new_test_ext().execute_with(|| {
        let hash: H256 = "ABC".using_encoded(blake2_256).into();
        let proposal = make_remark_proposal(hash.clone());
        let prop_id = 1;
        let src_id = 1;
        let r_id = bridge::derive_resource_id(src_id, b"hash");
        let resource = b"Example.remark".to_vec();

        assert_ok!(Bridge::set_threshold(Origin::root(), TEST_THRESHOLD,));
        assert_ok!(Bridge::add_relayer(Origin::root(), RELAYER_A));
        assert_ok!(Bridge::add_relayer(Origin::root(), RELAYER_B));
        assert_ok!(Bridge::whitelist_chain(Origin::root(), src_id));
        assert_ok!(Bridge::set_resource(Origin::root(), r_id, resource));

        assert_ok!(Bridge::acknowledge_proposal(
            Origin::signed(RELAYER_A),
            prop_id,
            src_id,
            r_id,
            Box::new(proposal.clone())
        ));
        assert_ok!(Bridge::acknowledge_proposal(
            Origin::signed(RELAYER_B),
            prop_id,
            src_id,
            r_id,
            Box::new(proposal.clone())
        ));

        event_exists(RawEvent::Remark(hash));
    })
}

#[test]
fn execute_remark_bad_origin() {
    new_test_ext().execute_with(|| {
        let hash: H256 = "ABC".using_encoded(blake2_256).into();

        assert_ok!(Example::remark(Origin::signed(Bridge::account_id()), hash));
        // Don't allow any signed origin except from bridge addr
        assert_noop!(
            Example::remark(Origin::signed(RELAYER_A), hash),
            DispatchError::BadOrigin
        );
        // Don't allow root calls
        assert_noop!(
            Example::remark(Origin::root(), hash),
            DispatchError::BadOrigin
        );
    })
}

#[test]
fn transfer() {
    new_test_ext().execute_with(|| {
        // Check inital state
        let bridge_id: u64 = Bridge::account_id();
        assert_eq!(Balances::free_balance(&bridge_id), ENDOWED_BALANCE);
        // Transfer and check result
        assert_ok!(Example::transfer(
            Origin::signed(Bridge::account_id()),
            RELAYER_A,
            10
        ));
        assert_eq!(Balances::free_balance(&bridge_id), ENDOWED_BALANCE - 10);
        assert_eq!(Balances::free_balance(RELAYER_A), ENDOWED_BALANCE + 10);

        assert_events(vec![Event::balances(balances::RawEvent::Transfer(
            Bridge::account_id(),
            RELAYER_A,
            10,
        ))]);
    })
}

#[test]
fn mint_erc721() {
    new_test_ext().execute_with(|| {
        let token_id = U256::from(99);
        let recipient = RELAYER_A;
        let metadata = vec![1, 1, 1, 1];
        let bridge_id: u64 = Bridge::account_id();

        // Token doesn't yet exist
        assert_eq!(Erc721::tokens(token_id), None);
        // Mint
        assert_ok!(Example::mint_erc721(
            Origin::signed(bridge_id),
            recipient,
            token_id,
            metadata.clone()
        ));
        // Ensure token exists
        assert_eq!(
            Erc721::tokens(token_id).unwrap(),
            Erc721Token {
                id: token_id,
                metadata: metadata.clone()
            }
        );
        // Cannot mint same token
        assert_noop!(
            Example::mint_erc721(
                Origin::signed(bridge_id),
                recipient,
                token_id,
                metadata.clone()
            ),
            erc721::Error::<Test>::TokenAlreadyExists
        );
    })
}

#[test]
fn create_sucessful_transfer_proposal() {
    new_test_ext().execute_with(|| {
        let prop_id = 1;
        let src_id = 1;
        let r_id = bridge::derive_resource_id(src_id, b"transfer");
        let resource = b"Example.transfer".to_vec();
        let proposal = make_transfer_proposal(RELAYER_A, 10);

        assert_ok!(Bridge::set_threshold(Origin::root(), TEST_THRESHOLD,));
        assert_ok!(Bridge::add_relayer(Origin::root(), RELAYER_A));
        assert_ok!(Bridge::add_relayer(Origin::root(), RELAYER_B));
        assert_ok!(Bridge::add_relayer(Origin::root(), RELAYER_C));
        assert_ok!(Bridge::whitelist_chain(Origin::root(), src_id));
        assert_ok!(Bridge::set_resource(Origin::root(), r_id, resource));

        // Create proposal (& vote)
        assert_ok!(Bridge::acknowledge_proposal(
            Origin::signed(RELAYER_A),
            prop_id,
            src_id,
            r_id,
            Box::new(proposal.clone())
        ));
        let prop = Bridge::votes(src_id, (prop_id.clone(), proposal.clone())).unwrap();
        let expected = bridge::ProposalVotes {
            votes_for: vec![RELAYER_A],
            votes_against: vec![],
            status: bridge::ProposalStatus::Initiated,
            expiry: ProposalLifetime::get() + 1,
        };
        assert_eq!(prop, expected);

        // Second relayer votes against
        assert_ok!(Bridge::reject_proposal(
            Origin::signed(RELAYER_B),
            prop_id,
            src_id,
            r_id,
            Box::new(proposal.clone())
        ));
        let prop = Bridge::votes(src_id, (prop_id.clone(), proposal.clone())).unwrap();
        let expected = bridge::ProposalVotes {
            votes_for: vec![RELAYER_A],
            votes_against: vec![RELAYER_B],
            status: bridge::ProposalStatus::Initiated,
            expiry: ProposalLifetime::get() + 1,
        };
        assert_eq!(prop, expected);

        // Third relayer votes in favour
        assert_ok!(Bridge::acknowledge_proposal(
            Origin::signed(RELAYER_C),
            prop_id,
            src_id,
            r_id,
            Box::new(proposal.clone())
        ));
        let prop = Bridge::votes(src_id, (prop_id.clone(), proposal.clone())).unwrap();
        let expected = bridge::ProposalVotes {
            votes_for: vec![RELAYER_A, RELAYER_C],
            votes_against: vec![RELAYER_B],
            status: bridge::ProposalStatus::Approved,
            expiry: ProposalLifetime::get() + 1,
        };
        assert_eq!(prop, expected);

        assert_eq!(Balances::free_balance(RELAYER_A), ENDOWED_BALANCE + 10);
        assert_eq!(
            Balances::free_balance(Bridge::account_id()),
            ENDOWED_BALANCE - 10
        );

        assert_events(vec![
            Event::bridge(bridge::RawEvent::VoteFor(src_id, prop_id, RELAYER_A)),
            Event::bridge(bridge::RawEvent::VoteAgainst(src_id, prop_id, RELAYER_B)),
            Event::bridge(bridge::RawEvent::VoteFor(src_id, prop_id, RELAYER_C)),
            Event::bridge(bridge::RawEvent::ProposalApproved(src_id, prop_id)),
            Event::balances(balances::RawEvent::Transfer(
                Bridge::account_id(),
                RELAYER_A,
                10,
            )),
            Event::bridge(bridge::RawEvent::ProposalSucceeded(src_id, prop_id)),
        ]);
    })
}
