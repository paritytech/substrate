// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! # Block building process
//!
//! Block building process depends on [`sc_consensus_aura`]
//!
//!
//! - [`cumulus_client_collator::Collator`]
//! - [`cumulus_client_consenus_common::ParachainConsensus`]
//! - [`sc_consensus_slots::SimpleSlotWorker`]
//! - [`sc_consensus_aura::AuraWorker`]
//! - [`sc_basic_authorship_ver::BasicAuthorshipVer`]
//!
//! ```
//! sequenceDiagram
//!    Collator->>ParachainConsensus: produce_candidate
//!    ParachainConsensus->>AuraConsensus: produce_candidate
//!    AuraConsensus->>SimpleSlotWorker: on_slot
//!    SimpleSlotWorker->>AuraWorker: claim_slot
//!    alt do i as collator know private key of given slot author
//!        AuraWorker->>SimpleSlotWorker: generate shuffling seed (as inherent)
//!        SimpleSlotWorker->>BasicAuthorshipVer: propose
//!        note over BasicAuthorshipVer: build block
//!        BasicAuthorshipVer->>Collator: <block>
//!
//!    else
//!        SimpleSlotWorker-x Collator:
//!    end
//! ```
//!
//! In origin substrate impl there are three limits, as soon one of them is exceeded block
//! producation is finalized and block is broadcastet:
//! - block size limit
//! - block weight limit (sum of weights of all transactions)
//! - block execution time limit (actual execution time of)
//!
//!
//! In mangata transaction included into block `N` is executed in block `N+1` because of
//! shuffling(VER prevention) mechanism.
//!
//! We want to avoid situation where block would by filled with
//! txs to that point that in the following block there would be no space left for inclusion of
//! following txs
//!
//! imagine that we have X time for tx processing in every block.
///```
/// 	|--------------|    |--------------|    |--------------|
/// 	|    Block N   |    |    Block N+1 |    |    Block N+2 |
/// 	|--------------|    |--------------|    |--------------|
/// 	| EXECUTED:    |    | EXECUTED:    |    | EXECUTED:    |
/// 	|              |    | TX1:  0.1 X  |    |              |
/// 	|              |    | TX2:  0.1 X  |    |              |
/// 	|--------------|    | TX3:  0.1 X  |    |--------------|
/// 	| INCLUDED:    |    | TX4:  0.1 X  |    | INCLUDED:    |
/// 	| TX1:  0.1 X  |    | TX5:  0.1 X  |    | TX11: 0.1 X  |
/// 	| TX2:  0.1 X  |    | TX6:  0.1 X  |    | TX12:  0.1 X |
/// 	| TX3:  0.1 X  |    | TX7:  0.1 X  |    |              |
/// 	| TX4:  0.1 X  |    | TX8:  0.1 X  |    |              |
/// 	| TX5:  0.1 X  |    | TX9:  0.1 X  |    |              |
/// 	| TX6:  0.1 X  |    | TX10: 0.1 X  |    |              |
/// 	| TX7:  0.1 X  |    |--------------|    |              |
/// 	| TX8:  0.1 X  |    | INCLUDED:    |    |              |
/// 	| TX9:  0.1 X  |    |              |    |              |
/// 	| TX10: 0.1 X  |    |              |    |              |
/// 	|--------------|    |--------------|    |--------------|
///
///
///
/// 	|--------------|    |--------------|    |--------------|
/// 	|    Tx pool   |    |  Tx pool     |    | Tx pool      |
/// 	|--------------|    |--------------|    |--------------|
/// 	| TX1          |    | TX11         |    |              |
/// 	| TX2          |    | TX12         |    |              |
/// 	| TX3          |    |              |    |              |
/// 	| TX4          |    |              |    |              |
/// 	| TX5          |    |              |    |              |
/// 	| TX6          |    |              |    |              |
/// 	| TX7          |    |              |    |              |
/// 	| TX8          |    |              |    |              |
/// 	| TX9          |    |              |    |              |
/// 	| TX10         |    |              |    |              |
/// 	|--------------|    |--------------|    |--------------|
/// ```
///
/// **In block `N+1` ther is no room for any transaction to be included because execution of
/// previous block will exceed block limits.**
///
///
/// For that reason we divide every slot into 2 part, and we apply `X/2` for each of them.
/// As a result we know that execution of previous block extrinsics will use at most 50% of the
/// resources (time, size, weight) and remainig time can be used for validation and inclusion of txs
/// submitted by users.
///
///```
/// 	|--------------|    |--------------|    |--------------|
/// 	|    Block N   |    |    Block N+1 |    |    Block N+2 |
/// 	|--------------|    |--------------|    |--------------|
/// 	| EXECUTED:    |    | EXECUTED:    |    | EXECUTED:    |
/// 	|              |    | TX1:  0.1 X  |    | TX6:  0.1 X  |
/// 	|              |    | TX2:  0.1 X  |    | TX7:  0.1 X  |
/// 	|--------------|    | TX3:  0.1 X  |    | TX8:  0.1 X  |
/// 	| INCLUDED:    |    | TX4:  0.1 X  |    | TX9:  0.1 X  |
/// 	| TX1:  0.1 X  |    | TX5:  0.1 X  |    | TX10: 0.1 X  |
/// 	| TX2:  0.1 X  |    |--------------|    |--------------|
/// 	| TX3:  0.1 X  |    | INCLUDED:    |    | INCLUDED:    |
/// 	| TX4:  0.1 X  |    | TX6:  0.1 X  |    | TX11:  0.1 X |
/// 	| TX5:  0.1 X  |    | TX7:  0.1 X  |    | TX12:  0.1 X |
/// 	|              |    | TX8:  0.1 X  |    |              |
/// 	|              |    | TX9:  0.1 X  |    |              |
/// 	|              |    | TX10: 0.1 X  |    |              |
/// 	|              |    |              |    |              |
/// 	|              |    |              |    |              |
/// 	|--------------|    |--------------|    |--------------|
///
///
///
/// 	|--------------|    |--------------|    |--------------|
/// 	|    Tx pool   |    |  Tx pool     |    | Tx pool      |
/// 	|--------------|    |--------------|    |--------------|
/// 	| TX1          |    | TX11         |    |              |
/// 	| TX2          |    | TX12         |    |              |
/// 	| TX3          |    |              |    |              |
/// 	| TX4          |    |              |    |              |
/// 	| TX5          |    |              |    |              |
/// 	| TX6          |    |              |    |              |
/// 	| TX7          |    |              |    |              |
/// 	| TX8          |    |              |    |              |
/// 	| TX9          |    |              |    |              |
/// 	| TX10         |    |              |    |              |
/// 	|              |    |              |    |              |
/// 	|              |    |              |    |              |
/// 	|              |    |              |    |              |
/// ```
///
///
/// so comparing to origin impl which can be presented as
///
///
/// ```
///        execution time/size/weight limits (X)
/// <-------------------------------------------------->
///
/// |--------------------------------------------------|
/// |                                                  |
/// | collectin txs from pool and executing them       |
/// |                                                  |
/// |--------------------------------------------------|
/// ```
///
/// In mangata its more like
///
///
///        X/2                       X/2
/// <--------------------->-<-------------------------->
/// |--------------------------------------------------|
/// |                      |                           |
/// |   execution of       |  collecting tx from pool  |
/// |   previous block txs |                           |
/// |                      |                           |
/// |--------------------------------------------------|
mod basic_authorship;

pub use crate::basic_authorship::{Proposer, ProposerFactory, DEFAULT_BLOCK_SIZE_LIMIT};
