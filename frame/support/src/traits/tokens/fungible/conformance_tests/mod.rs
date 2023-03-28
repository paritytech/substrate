/// Temporary module to hold the conformance tests for the Fungible trait,
/// until it is abstracted into pallet-agnostic macro/s and moved outside
/// of the balances module.
///
/// TODO: Decouple these tests from balances and abstract them into a macro so that they can be
/// used by any pallet that implements any `fungible` traits.
///
/// Open question: Do we need conformance tests for 'unbalanced' traits?
pub mod balanced;
pub mod balanced_hold;
pub mod handle_imbalance_drop;
pub mod inspect;
pub mod inspect_freeze;
pub mod inspect_hold;
pub mod mutate;
pub mod mutate_freeze;
pub mod mutate_hold;
