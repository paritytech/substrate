use alloc::{
	string::{String, ToString},
	vec::Vec,
};
use ibc::signer::Signer;

pub fn get_dummy_bech32_account() -> String {
	"cosmos1wxeyh7zgn4tctjzs0vtqpc6p5cxq5t2muzl7ng".to_string()
}

pub fn get_dummy_proof() -> Vec<u8> {
	"Y29uc2Vuc3VzU3RhdGUvaWJjb25lY2xpZW50LzIy".as_bytes().to_vec()
}

pub fn get_dummy_account_id() -> Signer {
	"0CDA3F47EF3C4906693B170EF650EB968C5F4B2C".parse().unwrap()
}
