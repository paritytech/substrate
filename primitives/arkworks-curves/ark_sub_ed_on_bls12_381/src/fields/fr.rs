use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "6554484396890773809930967563523245729705921265872317281365359162392183254199"]
#[generator = "6"]
pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;
