/// Temporary module to hold the conformance tests for the Fungible trait,
/// until it is abstracted into pallet-agnostic macro/s and moved outside
/// of the balances module.
///
/// TODO: Decouple these tests from balances and abstract them into a macro so that they can be
/// used by any pallet that implements any `fungible` traits.
///
/// Open question: Do we need conformance tests for 'unbalanced' traits?
use super::*;
mod balanced;
mod balanced_hold;
mod handle_imbalance_drop;
mod inspect;
mod inspect_freeze;
mod inspect_hold;
pub mod mutate;
pub mod mutate_freeze;
pub mod mutate_hold;
