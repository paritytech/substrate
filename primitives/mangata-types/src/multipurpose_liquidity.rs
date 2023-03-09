#![cfg_attr(not(feature = "std"), no_std)]
use codec::{Decode, Encode};
use scale_info::TypeInfo;
use sp_runtime::RuntimeDebug;

#[derive(Eq, PartialEq, Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
pub enum ActivateKind {
	AvailableBalance,
	StakedUnactivatedReserves,
	UnspentReserves,
}

#[derive(Eq, PartialEq, Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
pub enum BondKind {
	AvailableBalance,
	ActivatedUnstakedReserves,
	UnspentReserves,
}
