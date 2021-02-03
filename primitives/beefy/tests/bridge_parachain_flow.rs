// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! A set of examples how the bridge would operate.

// struct MerkleMountainRangeLeaf(
//     (
//         /// This is populated only for epoch blocks and contains a merkle root of the NEXT
//         /// validator set.
//         Option<MerkleRootOfPublicKeys>,
//         ///
//         MerkleRootOfParaHeads,
//         ///
//         ParentBlockHash,
//     ),
// )
//
// #[test]
// fn light_client_andres_case() {
// 	// we submit block 10 (1st phase)
//
// 	// an app submitting a mmr proof against this hash from block10
//
//
// 	// we are at block 10 doing second phase for it. (validatorset=1)
// 	..
//
// 	// we got block 20 (validatorset=1)
//
// 	..
// }
//
// #[test]
// fn solidity_light_client_makes_progress() {
// 	let lc = SolidityContractOnEthereum;
// 	//
// 	lc.submit(PartialSignedCommitment {});
//
// 	// For epoch blocks
// 	lc.submit(PartialSignedCommitment {}, MMMProofOfMerkleProofOfPublicKeys);
//
// 	//TODO: 2nd phase verification
// 	lc.submit_signatures(
// 		Vec<(idx, PublicKey)>,
// 		Vec<(idx, Signature)>,
// 		MerkleProofOfPublicKeys,
// 		MerkleProofOfSignatures,
// 	);
// }
//
// #[test]
// fn light_client_makes_progress() {
// 	let lc = ...;
//
// 	lc.submit(SignedCommitment, None);
//
// 	// if the validator_set_id_changes we require an extra proof.
// 	lc.submit(SignedCommitment, Some(Vec<PublicKey> + MMRProofForTheValidatorMerkleRoot));
// }
//
// #[test]
// fn can_process_bridge_messages() {
// 	// ParachainY -HRMP->ParachainX
// 	// ParachainX -> SmartContractX
// 	//
// 	//
// 	//
// 	// RelayChain -> BridgeSmartContract
// 	//
// 	//
// 	//     x
// 	// ........................... Relay Chian Blocks
// 	// c c c c c c | c c c c c c c Generated comittment (by BEEFY)
// 	// ^   ^   ^   ^               Commitment seen by the light client
// 	//             *               2nd-phase proven commitments.
// 	//     l   l
// 	//
// 	//     x
// 	// ....a......................
// 	// c c c c c c | c c c c c c c
// 	// ^           ^
// 	//             *
//
//
//
// 	let heavy_proof = (
// 		ParachainSpecificProof, // for instance storage proof on a parachain
// 		ParachainHead,
// 		MerkleProofOfParachainHeadAtTheRelayChainBlockXWhenParachainHeadGotIncluded,
// 		//MmrProofOfRelayChainBlock,
// 		Block10
// 	);
//
// 	let lighter_proof = (
// 		MmrProofOfRelayChainBlock,
//
// 	);
// }
