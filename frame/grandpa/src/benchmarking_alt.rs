#![cfg(any(feature = "runtime-benchmarks", test))]

use super::{Pallet as Grandpa, *};
use frame_system::RawOrigin;
use sp_core::H256;

#[frame_support::benchmark]
fn bench_name(x: LinearComponent<0, 1>) {
    // NOTE: generated with the test below `test_generate_equivocation_report_blob`.
    // the output should be deterministic since the keys we use are static.
    // with the current benchmark setup it is not possible to generate this
    // programatically from the benchmark setup.
    const EQUIVOCATION_PROOF_BLOB: [u8; 257] = [
        1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 136, 220, 52, 23,
        213, 5, 142, 196, 180, 80, 62, 12, 18, 234, 26, 10, 137, 190, 32,
        15, 233, 137, 34, 66, 61, 67, 52, 1, 79, 166, 176, 238, 207, 48,
        195, 55, 171, 225, 252, 130, 161, 56, 151, 29, 193, 32, 25, 157,
        249, 39, 80, 193, 214, 96, 167, 147, 25, 130, 45, 42, 64, 208, 182,
        164, 10, 0, 0, 0, 0, 0, 0, 0, 234, 236, 231, 45, 70, 171, 135, 246,
        136, 153, 38, 167, 91, 134, 150, 242, 215, 83, 56, 238, 16, 119, 55,
        170, 32, 69, 255, 248, 164, 20, 57, 50, 122, 115, 135, 96, 80, 203,
        131, 232, 73, 23, 149, 86, 174, 59, 193, 92, 121, 76, 154, 211, 44,
        96, 10, 84, 159, 133, 211, 56, 103, 0, 59, 2, 96, 20, 69, 2, 32,
        179, 16, 184, 108, 76, 215, 64, 195, 78, 143, 73, 177, 139, 20, 144,
        98, 231, 41, 117, 255, 220, 115, 41, 59, 27, 75, 56, 10, 0, 0, 0, 0,
        0, 0, 0, 128, 179, 250, 48, 211, 76, 10, 70, 74, 230, 219, 139, 96,
        78, 88, 112, 33, 170, 44, 184, 59, 200, 155, 143, 128, 40, 222, 179,
        210, 190, 84, 16, 182, 21, 34, 94, 28, 193, 163, 226, 51, 251, 134,
        233, 187, 121, 63, 157, 240, 165, 203, 92, 16, 146, 120, 190, 229,
        251, 129, 29, 45, 32, 29, 6
    ];

    let equivocation_proof1: sp_finality_grandpa::EquivocationProof<H256, u64> =
        Decode::decode(&mut &EQUIVOCATION_PROOF_BLOB[..]).unwrap();

    let equivocation_proof2 = equivocation_proof1.clone();

    #[extrinsic_call]
    sp_finality_grandpa::check_equivocation_proof(equivocation_proof1);

    // Post condition verification
    assert!(sp_finality_grandpa::check_equivocation_proof(equivocation_proof2));
}
