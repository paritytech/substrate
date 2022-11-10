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

//! # Docs
//! [!!! HERE
//! !!!](https://storage.googleapis.com/mangata-docs-node/sc_basic_authorship_ver/basic_authorship/index.html)

#[cfg(doc)]
use aquamarine::aquamarine;

#[cfg_attr(doc, aquamarine::aquamarine)]
/// # Block building process
///
/// Block production is initiated by `Collator` impl comming from `cumulus` repository. Whole
/// pipline looks more & less as on diagram below
///
/// ```mermaid
/// sequenceDiagram
///    Collator->>ParachainConsensus: produce_candidate
///    ParachainConsensus->>AuraConsensus: produce_candidate
///    AuraConsensus->>SimpleSlotWorker: on_slot
///    SimpleSlotWorker->>AuraWorker: claim_slot
///    alt do i as collator know private key of given slot author
///        AuraWorker->>SimpleSlotWorker: generate shuffling seed (as inherent)
///        SimpleSlotWorker->>BasicAuthorshipVer: propose
///        note over BasicAuthorshipVer: build block
///        BasicAuthorshipVer->>Collator: block
///    else
///        SimpleSlotWorker-x Collator: x
///    end
/// ```
///
/// see references for particular actors:
///
/// - [cumulus_client_collator::Collator](https://storage.googleapis.com/mangata-docs-node/cumulus_client_collator/struct.Collator.html)
/// - [cumulus_client_consenus_common::ParachainConsensus](https://storage.googleapis.com/mangata-docs-node/cumulus_client_consensus_common/trait.ParachainConsensus.html)
/// - [cumulus_client_consenus_aura::AuraConsensus](https://storage.googleapis.com/mangata-docs-node/cumulus_client_consensus_aura/struct.AuraConsensus.html)
/// - [sc_consensus_slots::SimpleSlotWorker](https://storage.googleapis.com/mangata-docs-node/sc_consensus_slots/trait.SimpleSlotWorker.html)
/// - `sc_consensus_aura::AuraWorker` - private struct
/// - [sc_basic_authorship_ver::Proposer](https://storage.googleapis.com/mangata-docs-node/sc_basic_authorship_ver/struct.Proposer.html)
///
///
///
/// # Block production logic
///
/// In origin substrate impl there are three limits, as soon one of them is exceeded block
/// producation is finalized and block is broadcastet:
/// - block size limit
/// - block weight limit (sum of weights of all transactions)
/// - block execution time limit (actual execution time of)
///
///
/// In mangata transaction included into block `N` is executed in block `N+1` because of
/// shuffling(VER prevention) mechanism.
///
/// We want to avoid situation where block would by filled with
/// txs to that point that in the following block there would be no space left for inclusion of
/// following txs
///
/// imagine that we have X time for tx processing in every block.
/// **In block `N+1` ther would no room for any transaction to be included because execution of
/// previous block will exceed block limits.**
///```
/// 
/// |--------------|    |--------------|    |--------------|
/// |    Block N   |    |    Block N+1 |    |    Block N+2 |
/// |--------------|    |--------------|    |--------------|
/// | EXECUTED:    |    | EXECUTED:    |    | EXECUTED:    |
/// |--------------|    | TX1:  0.25X  |    |--------------|
/// | INCLUDED:    |    | TX2:  0.25X  |    | INCLUDED:    |
/// | TX1:  0.25X  |    | TX3:  0.25X  |    | TX5: 0.25X   |
/// | TX2:  0.25X  |    | TX4:  0.25X  |    | TX6: 0.25X   |
/// | TX3:  0.25X  |    |--------------|    |              |
/// | TX4:  0.25X  |    | INCLUDED:    |    |              |
/// |              |    | TX5:  0.25X  |    |              |
/// |              |    | TX6:  0.25X  |    |              |
/// |--------------|    |--------------|    |--------------|
///       ⇧⇧⇧⇧                ⇧⇧⇧⇧                ⇧⇧⇧⇧      
/// |--------------|    |--------------|    |--------------|
/// |    Tx pool   |    |  Tx pool     |    | Tx pool      |
/// |--------------|    |--------------|    |--------------|
/// | TX1          |    | TX5          |    |              |
/// | TX2          |    | TX6          |    |              |
/// | TX3          |    |              |    |              |
/// | TX4          |    |              |    |              |
/// |--------------|    |--------------|    |--------------|
/// ```
///
/// For that reason we divide every slot into 2 part, and we apply `X/2` for each of them.
/// As a result we know that execution of previous block extrinsics will use at most 50% of the
/// resources (time, size, weight) and remainig time can be used for validation and inclusion of txs
/// submitted by users.
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
///```
///        X/2                       X/2
/// <--------------------->-<-------------------------->
/// |--------------------------------------------------|
/// |                      |                           |
/// |   execution of       |  collecting tx from pool  |
/// |   previous block txs |                           |
/// |                      |                           |
/// |--------------------------------------------------|
/// ```
///
/// As a result blocks will be constructed as follows
///
///```
/// 
/// |--------------|    |--------------|    |--------------|
/// |    Block N   |    |    Block N+1 |    |    Block N+2 |
/// |--------------|    |--------------|    |--------------|
/// | EXECUTED:    |    | EXECUTED:    |    | EXECUTED:    |
/// |--------------|    | TX1:  0.25X  |    |--------------|
/// | INCLUDED:    |    | TX2:  0.25X  |    | INCLUDED:    |
/// | TX1:  0.25X  |    |--------------|    | TX5: 0.25X   |
/// | TX2:  0.25X  |    | INCLUDED:    |    | TX6: 0.25X   |
/// |              |    | TX3:  0.25X  |    |              |
/// |              |    | TX4:  0.25X  |    |              |
/// |              |    |              |    |              |
/// |              |    |              |    |              |
/// |--------------|    |--------------|    |--------------|
///       ⇧⇧⇧⇧                ⇧⇧⇧⇧                ⇧⇧⇧⇧      
/// |--------------|    |--------------|    |--------------|
/// |    Tx pool   |    |  Tx pool     |    | Tx pool      |
/// |--------------|    |--------------|    |--------------|
/// | TX1          |    | TX5          |    | TX5          |
/// | TX2          |    | TX6          |    | TX6          |
/// | TX3          |    |              |    |              |
/// | TX4          |    |              |    |              |
/// |--------------|    |--------------|    |--------------|
/// ```
///
///
/// # Block construction vs block execution
/// Block construction & block execution(broadcasted block is executed by every network participant)
/// are two distinct logical flows that results with exactly the same state.
/// There is number of differences, some of them are:
/// - block construction process happens in native/host code, all interactions with storage happens
/// through runtime api, while block execution happens entirely at runtime. Native code can access
/// runtime while runtime has no access to native code (rocksdb database, reversable txs etc)
/// - during block production txs are fetched from StorageQeueu one by one inside revertable
/// transaction. When slot limits are reached the most recent tx (that exceeds the limit) is brought
/// back to into the queue by reverting last transaction that dequeues single tx. None of that
/// happens during block execution, number of txs that should be fetched is already set and passed
/// in block header (by block builder)
/// - during block production seed is generated by siging previous block seed using collator private
/// key while during execution new seed is only validated by using previous seed & collator public
/// key.
/// - during block production txs included into the block **from transaction
/// pool** are actually executed (to check if txs will not exceed block execution time limit) but
/// eventually all of them are reverted because they are meant to be executed in following block
/// (after shuffling). During block execution these txs are not executed(they will be in following
/// block but we still consider if included txs will fit into single block) because at runtime its
/// not possible to revert changes made by particular transaction
///
/// for block construction details see [`basic_authorship::Proposer`]
/// for block executive details see [frame_executive](https://storage.googleapis.com/mangata-docs-node/frame_executive/struct.Executive.html)
pub mod basic_authorship;

pub use crate::basic_authorship::{Proposer, ProposerFactory, DEFAULT_BLOCK_SIZE_LIMIT};
