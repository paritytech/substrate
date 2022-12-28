use crate::Config;

/// Specifies the constraints for computing a pairing in the BLS12-377 bilinear
/// group.
pub type PairingVar = ark_r1cs_std::pairing::bls12::PairingVar<Config>;

#[test]
fn test() {
    use crate::Bls12_377;
    ark_curve_constraint_tests::pairing::bilinearity_test::<Bls12_377, PairingVar>().unwrap();
    ark_curve_constraint_tests::pairing::g2_prepare_consistency_test::<Bls12_377, PairingVar>()
        .unwrap();
}
