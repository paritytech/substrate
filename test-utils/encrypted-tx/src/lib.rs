#![cfg_attr(not(feature = "std"), no_std)]

use sp_runtime::traits::DigestFor;
use sp_runtime::DigestItem;

pub const ALICE_COLLATOR_ID: u32 = 1;
pub const ALICE_ACCOUNT_ID: [u8;32]  = [2, 10, 16, 145, 52, 31, 229, 102, 75, 250, 23, 130, 213, 224, 71, 121, 104, 144, 104, 201, 22, 176, 76, 179, 101, 236, 49, 83, 117, 86, 132, 217];
pub const ALICE_PUB_KEY: [u8;33] = [2, 10, 16, 145, 52, 31, 229, 102, 75, 250, 23, 130, 213, 224, 71, 121, 104, 144, 104, 201, 22, 176, 76, 179, 101, 236, 49, 83, 117, 86, 132, 217, 161];
pub const DUMMY_COLLATOR_ID: u32 = 2;
pub const DUMMY_ACCOUNT_ID: [u8;32]  = [0u8;32];
pub const UNKNOWN_COLLATOR_ID: u32 = 3;
pub const BOB_COLLATOR_ID: u32 = 4;
pub const BOB_ACCOUNT_ID: [u8;32]  = [2, 10, 16, 145, 52, 31, 229, 102, 75, 250, 23, 130, 213, 224, 71, 121, 104, 144, 104, 201, 22, 176, 76, 179, 101, 236, 49, 83, 117, 86, 132, 217];
pub const BOB_PUB_KEY: [u8;33] = [2, 10, 16, 145, 52, 31, 229, 102, 75, 250, 23, 130, 213, 224, 71, 121, 104, 144, 104, 201, 22, 176, 76, 179, 101, 236, 49, 83, 117, 86, 132, 217, 161];


#[cfg(feature = "std")]
use sc_consensus_babe::CompatibleDigestItem;

#[cfg(feature = "std")]
pub fn create_digest() -> DigestFor<substrate_test_runtime::Block>{
    inject_collator_id(ALICE_COLLATOR_ID)
}

#[cfg(feature = "std")]
pub fn inject_collator_id(collator: u32) -> DigestFor<substrate_test_runtime::Block>{
    let mut digests : DigestFor<substrate_test_runtime::Block> = Default::default();
    let babe_pre = sc_consensus_babe::PreDigest::SecondaryPlain(sc_consensus_babe::SecondaryPlainPreDigest{
        authority_index: collator,
        slot_number: Default::default(),
    });
    digests.push(DigestItem::babe_pre_digest(babe_pre));
    digests
}
