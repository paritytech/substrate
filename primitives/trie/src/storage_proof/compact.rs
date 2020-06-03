// Copyright 2020 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ! Trie storage proofs that are a compacted collection of encoded nodes.

/// A collection on encoded and compacted trie nodes.
/// Nodes are sorted by trie node iteration order, and some hash
/// and/or values are ommitted (they can be either calculated from
/// proof content or completed by proof input).
pub type ProofCompacted = Vec<Vec<u8>>;


