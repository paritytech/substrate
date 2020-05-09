use super::*;
use mock::{
	Sudo, Origin, Test, Call, Priveleged, PrivelegedCall
}; 
// use node_primitives::AccountId
	// , Balance, Signature
// };


#[test]
fn basics(){
	// TODO make sure this root_key is correctly set before each test
	// root_key taken from chain_spec.rs

	// let root_key = hex![
	// 	"9ee5e5bdc0ec239eb164f865ecc345ce4c88e76ee002e0f7e318097347471809"
	// ].into();

	// let call = Box::new(Call::Priveleged())
	// Sudo::sudo(
	// 	Origin::signed(root_key), 
	// 	Box::new(Priveleged::privileged_function(Origin::signed(root_key)))
	// );
	assert_eq!(1,1)
}

// // From sudo docs: "you can execute these privileged functions by calling `sudo` with the sudo 
// // key account." 
// // so here i am thinking the 'sudo key' is just an AccountId so I can just pull
// // the AccountId used as a the root_key in chain_spec.rs and use this 
// // Origin::signed() enum. (Not sure actually sure what it means to be signed in this case)

// let root_key: AccountId = hex![
// 	"9ee5e5bdc0ec239eb164f865ecc345ce4c88e76ee002e0f7e318097347471809"
// ].into();

// let arbirtrary_key: AccountId = hex![
// 	"8ee5e5bdc0ec239eb164f865ecc345ce4c88e76ee002e0f7e319087347471908"
// ].into();

// // this should work
// Sudo::sudo(Origin::signed(root_key), privllege_fn(Origin::signed(root_key)))

// // this should emit Error::<T>::RequireSudo
// Sudo::sudo(Origin::signed(arbirtrary_key), privllege_fn(Origin::signed(arbirtrary_key)))

// where root_key: AcountId
// GenesisConfig::<Test>{
// 		key: root_key,
// 	}