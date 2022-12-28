//! Bls12-377 scalar field.
/// Roots of unity computed from modulus and R using this sage code:
///
/// ```ignore
/// q = 8444461749428370424248824938781546531375899335154063827935233455917409239041
/// R = 6014086494747379908336260804527802945383293308637734276299549080986809532403 # Montgomery R
/// s = 47
/// o = q - 1
/// F = GF(q)
/// g = F.multiplicative_generator()
/// g = F.multiplicative_generator()
/// assert g.multiplicative_order() == o
/// g2 = g ** (o/2**s)
/// assert g2.multiplicative_order() == 2**s
/// def into_chunks(val, width, n):
///     return [int(int(val) // (2 ** (width * i)) % 2 ** width) for i in range(n)]
/// print("Gen: ", g * R % q)
/// print("Gen: ", into_chunks(g * R % q, 64, 4))
/// print("2-adic gen: ", into_chunks(g2 * R % q, 64, 4))
/// ```
use ark_ff::fields::{Fp256, MontBackend, MontConfig};

#[derive(MontConfig)]
#[modulus = "8444461749428370424248824938781546531375899335154063827935233455917409239041"]
#[generator = "22"]
pub struct FrConfig;
pub type Fr = Fp256<MontBackend<FrConfig, 4>>;
