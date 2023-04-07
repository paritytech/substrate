/// Temporary module to hold the conformance tests for the Fungible trait,
/// until it is abstracted into pallet-agnostic macro/s and moved outside
/// of the balances module.
///
/// Open question: Do we need conformance tests for 'unbalanced' traits?
pub mod balanced;
pub mod mutate;
