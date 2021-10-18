#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use sp_runtime::traits::Block as BlockT;
use sp_runtime::AccountId32;
use sp_std::vec::Vec;


use frame_support::weights::Weight;


#[derive(Encode, Decode, PartialEq)]
pub enum ExtrinsicType<Hash>{
	DoublyEncryptedTx{
        doubly_encrypted_call: Vec<u8>,
        nonce: u32,
        weight: Weight,
        builder: AccountId32,
        executor: AccountId32,
	},
    SinglyEncryptedTx{
        identifier: Hash,
        singly_encrypted_call: Vec<u8>,
    },
    DecryptedTx{
        identifier: Hash,
        decrypted_call: Vec<u8>,
    },
	Other,
}


#[derive(Encode, Decode, PartialEq)]
pub struct EncryptedTx<Hash>{
    pub tx_id: Hash,
    pub data: Vec<u8>,
}

sp_api::decl_runtime_apis! {
	pub trait EncryptedTxApi
    {
        // creates extrinsic that decrypts doubly encrypted transaction
		fn create_submit_singly_encrypted_transaction(identifier: <Block as BlockT>::Hash, singly_encrypted_call: Vec<u8>) -> <Block as BlockT>::Extrinsic;

        // creates extrinsic that decrypts singly encrypted transaction
        fn create_submit_decrypted_transaction(identifier: <Block as BlockT>::Hash, decrypted_call: Vec<u8>, weight: Weight) -> <Block as BlockT>::Extrinsic;

		/// parses information about extrinsic
		fn get_type(extrinsic: <Block as BlockT>::Extrinsic) -> ExtrinsicType<<Block as BlockT>::Hash>;

        // fetches double encrypted transactions from FIFO queue
		fn get_double_encrypted_transactions(block_builder_id: &AccountId32) -> Vec<EncryptedTx<<Block as BlockT>::Hash>>;

        // fetches singly encrypted transactions from FIFO queue
		fn get_singly_encrypted_transactions(block_builder_id: &AccountId32) -> Vec<EncryptedTx<<Block as BlockT>::Hash>>;

        // fetches address assigned to authority id
		fn get_account_id(block_builder_id: u32) -> AccountId32;

        // use autority id to identify public key (from encrypted transactions apllet)
		fn get_authority_public_key(authority_id: &AccountId32) -> sp_core::ecdsa::Public;
	}
}
