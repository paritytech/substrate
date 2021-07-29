#![cfg(test)]

use super::mock::{new_test_ext, Erc721, Origin, Test, USER_A, USER_B, USER_C};
use super::*;
use frame_support::{assert_noop, assert_ok};
use sp_core::U256;

#[test]
fn mint_burn_tokens() {
    new_test_ext().execute_with(|| {
        let id_a: U256 = 1.into();
        let id_b: U256 = 2.into();
        let metadata_a: Vec<u8> = vec![1, 2, 3];
        let metadata_b: Vec<u8> = vec![4, 5, 6];

        assert_ok!(Erc721::mint(
            Origin::root(),
            USER_A,
            id_a,
            metadata_a.clone()
        ));
        assert_eq!(
            Erc721::tokens(id_a).unwrap(),
            Erc721Token {
                id: id_a,
                metadata: metadata_a.clone()
            }
        );
        assert_eq!(Erc721::token_count(), 1.into());
        assert_noop!(
            Erc721::mint(Origin::root(), USER_A, id_a, metadata_a.clone()),
            Error::<Test>::TokenAlreadyExists
        );

        assert_ok!(Erc721::mint(
            Origin::root(),
            USER_A,
            id_b,
            metadata_b.clone()
        ));
        assert_eq!(
            Erc721::tokens(id_b).unwrap(),
            Erc721Token {
                id: id_b,
                metadata: metadata_b.clone()
            }
        );
        assert_eq!(Erc721::token_count(), 2.into());
        assert_noop!(
            Erc721::mint(Origin::root(), USER_A, id_b, metadata_b.clone()),
            Error::<Test>::TokenAlreadyExists
        );

        assert_ok!(Erc721::burn(Origin::root(), id_a));
        assert_eq!(Erc721::token_count(), 1.into());
        assert!(!<Tokens>::contains_key(&id_a));
        assert!(!<TokenOwner<Test>>::contains_key(&id_a));

        assert_ok!(Erc721::burn(Origin::root(), id_b));
        assert_eq!(Erc721::token_count(), 0.into());
        assert!(!<Tokens>::contains_key(&id_b));
        assert!(!<TokenOwner<Test>>::contains_key(&id_b));
    })
}

#[test]
fn transfer_tokens() {
    new_test_ext().execute_with(|| {
        let id_a: U256 = 1.into();
        let id_b: U256 = 2.into();
        let metadata_a: Vec<u8> = vec![1, 2, 3];
        let metadata_b: Vec<u8> = vec![4, 5, 6];

        assert_ok!(Erc721::mint(
            Origin::root(),
            USER_A,
            id_a,
            metadata_a.clone()
        ));
        assert_ok!(Erc721::mint(
            Origin::root(),
            USER_A,
            id_b,
            metadata_b.clone()
        ));

        assert_ok!(Erc721::transfer(Origin::signed(USER_A), USER_B, id_a));
        assert_eq!(Erc721::owner_of(id_a).unwrap(), USER_B);

        assert_ok!(Erc721::transfer(Origin::signed(USER_A), USER_C, id_b));
        assert_eq!(Erc721::owner_of(id_b).unwrap(), USER_C);

        assert_ok!(Erc721::transfer(Origin::signed(USER_B), USER_A, id_a));
        assert_eq!(Erc721::owner_of(id_a).unwrap(), USER_A);

        assert_ok!(Erc721::transfer(Origin::signed(USER_C), USER_A, id_b));
        assert_eq!(Erc721::owner_of(id_b).unwrap(), USER_A);
    })
}
