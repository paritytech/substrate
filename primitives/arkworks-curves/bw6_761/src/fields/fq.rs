use ark_ff::fields::{Fp768, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "6891450384315732539396789682275657542479668912536150109513790160209623422243491736087683183289411687640864567753786613451161759120554247759349511699125301598951605099378508850372543631423596795951899700429969112842764913119068299"]
#[generator = "2"]
pub struct FqConfig;
pub type Fq = Fp768<MontBackend<FqConfig, 12>>;
