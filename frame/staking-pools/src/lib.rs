// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd. SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
// in compliance with the License. You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
// or implied. See the License for the specific language governing permissions and limitations under
// the License.

//! # Staking Pools
//!
//! decentralized, collective staking for the masses.
//!
//! ## High level design
//!
//! The main idea of staking pools is to allow more people to participate in the staking system,
//! without the need for all of them to cast *individual votes*. Recall that all votes need to be
//! processed in the staking election, and stored on-chain thereafter. Thus, being a 1st class
//! nominator puts a rather expensive cost on the chian. A staking pool is a platform for nominators
//! to gather their funds together, and cast their nominations as a single vote to the staking
//! system, should their opinions align with one another.
//!
//! Some nominators have an incentive to participate in a staking pool, since it will substantially
//! increase their possibility of receiving rewards. Recall that the 1st class nominator position is
//! reserved for accounts with the most amount of stake. The relay chain will benefit from staking
//! pools by increasing the total amount of tokens at stake, while still keeping them in the relay
//! chain, usable for governance and other purposes.
//!
//! ## V1 Specification
//!
//! > The staking pool is considered to be an extension that can *only* be used in a chain that
//! > contains the default substrate `pallet-staking`. In the implementation, we will most likely
//! > make it strictly depend on `pallet-staking` as well.
//!
//! #### Pool and the Founder
//!
//! Each pool has a founder that reserves a fixed (and relatively hefty amount of) deposit to
//! created the pool. The founder will decide which validators the entire pool will eventually
//! nominate. Thus, the same trust relationship that exist between nominators and validators also
//! exists between pool founders and their members. Each pool is associated with a single
//! inaccessible account (pool "Bonded Account"), derived from some pool identifier. This account is
//! always fully bonded (has no unlocked balance), and  will eventually act as the final 'Nominator'
//! that will submit a `nominate` extrinsic on behalf of the entire pool. The pool account is
//! forbidden from ever submitting any other transaction, other than `nominate` and a handful of
//! other well-known operations.
//!
//! Note that a pool is simply a normal nomination from the point of view of the staking pallet, and
//! there is absolutely no guarantee that the pool will become an *exposed* nominator. This is
//! entirely based on:s
//!
//! 1. whether the pool has enough collective stake to be part of the election snapshot.
//! 2. whether the mining algorithm includes the pool nominator in the election result.
//!
//! If the pool has sufficiently high amount of collective stake in it, the probability of both of
//! the previous points are very high. If exposed, and if an account triggers the appropriate
//! `payout_stakers`, the pool will receive rewards from the staking system in a secondary account
//! ("Reward Account") that is similarly inaccessible to anyone other than the pool's logic.
//!
//! #### Joining
//!
//! An account joins the pool (and become a "member") by accepting the consequence of putting a lock
//! on their account, which renders a part of their balance as unusable for transfers and other
//! purposes. This, in return, mints the equivalent tokens in the pool's bonded account, and
//! immediately triggers a `bond_extra` to the staking pallet. Note that these tokens are not really
//! part of the total issuance and are merely a derivative of the original tokens that is still in
//! the all member's account. The main purpose of this design over transferring the funds to the
//! pool's bonded account, or reserving them, is to allow the pool members to still use their funds
//! for governance and other lock-based actions, as long as they meet the conditions. This is
//! similar to how stakers of pallet-staking only lock their tokens for staking.
//!
//! Recall that all of the rewards go to an *unstaked* account (no compounding), meaning that the
//! *staked* amount of the pool does not automatically change (other than slashing, which we address
//! later). Therefore, the pool can always be in a state where a mapping of each member's *share* of
//! the pool's stake is known. Thus, each member's share of the *rewards being accumulated* (in the
//! reward account) is also known. A period of time during which the this mapping is static, and
//! rewards are being accumulated is called a "payout round", or "round" for short. A round can only
//! end if a "payout_all" function is called, where all of the rewards are payed out, without
//! anyone's share changing. This function can be called by anyone at any time, if they are willing
//! to pay its fees.
//!
//! Furthermore, any interaction that disrupts the mapping of shares needs to perform two actions
//! implicitly:
//!
//! 1. `payout_all`, where all leftover payouts are paid.
//! 2. `re_balance_all`, where all of the shares are re-computed.
//!
//! For example, an account wishing to join the pool must accept the burden of paying for the fees
//! of the previous two operations. Similarly, declaring the intention to leave the pool also needs
//! to payout and re-balance every other member.
//!
//! Each pool has a bounded number of participants (e.g. 512). This leads to congestion and the need
//! for a *joining policy*, resolving the situation when the pool is full and a new account intends
//! to join. Multiple joining policies could potentially, exist where the founder could decide on
//! which one the pool will operate on. Two common ones could be a "blocking FIFO" and/or a "stake
//! competition", where one can join a full pool only by forcefully removing a member who owns less
//! stake. A founder will typically be more interested in the latter, but participants prefer the
//! latter. For the V1 implementation of staking pools, a FIFO strategy should suffice.
//!
//! ### Leaving
//!
//! Leaving the pool has exactly the same implications as the staking system does. An intention to
//! leave (called `unbond_all`, which implies partial bonding is not possible) must be submitted by
//! a member, which will trigger an `unbond` to the staking pallet. Once the unbonding period is
//! passed (which is the same as the staking's bonding period), a separate `leave` transaction can
//! be called, which will, if successful, burn some tokens in the bonded account of the pool, and
//! removes the lock on the member's account. As noted, this will also trigger an automatic payout
//! of all the reward of the previous round, and re-balancing of shared for the upcoming round.
//!
//! > Interestingly, as long as the share mapping is untouched, unlike the normal staking pallet,
//! the rewards of the staking pool do not have any expiration date and can be claimed months and
//! years after being accumulated. This, combined with "private pools" could lead to interesting use
//! cases.
//!
//! ### Slashing
//!
//! Finally, leaving the pool brings up the topic of slashing. Recall that the pool has two
//! accounts: a "bonded" account and a "reward" amount. The rewards from the bonded account always
//! go to the reward account (without any compounding, aka. "unstaked"). If a slash happens, the
//! operations of the reward account remains exactly the same. Rewards are accumulated, perhaps a
//! bit less since some of the stake has been lost, and split between members pro rata, based on
//! their share.
//!
//! With regards to slashing, recall that (in the absence of slashing) the pool is always in a state
//! where the *sum of locks that it has put on members* is equal to its bonded account's stake
//! (`ledger.total` in staking). This means that a *user's share* (expressed as a ratio) multiplied
//! by the total stake of the pool's bonded account is exactly equal to the lock amount placed on
//! that member's account. Whilst this assumption is upheld, then leaving is trivial and
//! unambiguous. Each account will declare the intention to leave via `unbond_all`, wait for the
//! bonding duration, trigger `leave`, which makes some funds be unlocked in the pool's bonded
//! account. This amount will always be equal to the lock that was placed on the member's account.
//! To finalize leaving, the lock on the member's account is removed and the tokens in the pool's
//! bonded account are burned.
//!
//! > In essence, the pool's bonded account should NEVER have any unlocked tokens. They can only
//! become unlocked as the consequence of a member's `leave` transaction (which triggers a
//! `withdraw_unbonded` under the hood), in which case they are immediately burned, in return of the
//!
//! Therefore, the pool needs to be notified of any slashes, or essentially any unforeseen changes
//! to its total stake. Recall that since rewards are never compounded, the only possibility of the
//! bonded account's stake changing is slashing. Identifying the slashes is therefore simple, the
//! pallet only needs to track a single storage item which is the sum of all the locks that it has
//! placed on its members. Comparing that against `ledger.total` of staking should always be a
//! equality, except if a slash has occurred.
//!
//! Given the notification system, the pool can make sure the aforementioned assumption about the
//! shared and locked amounts are always help. Anytime it is identified that the pool's bonded stake
//! has reduced by `x`, this amount is split between all member proportional to their shares to
//! determine each member's slash amount. Then, the lock on the member's account is reduced, and the
//! excess tokens are burned on the member's original account to reflect the slash.
//!
//! For example, if alice had bonded 100 tokens in a pool of 200 tokens in total. Initially, she
//! only has a lock of 100 on her account. If the pool is slashed by 10 tokens, the pool will
//! identify this and determine 5 to be Alice's portion of the slash. 5 tokens from Alice's account
//! are burned, and the lock is reduced to 95 to maintain consistency and make further accounting
//! easier.
//!
//! > A hassle of this implementation is that we are treating locked currency as *slashable*,
//! while clearly they are not meant for it. This is why manual operations like minting and burning
//! are needed.
//!
//! ### Dissolving
//!
//! ## V2 features:
//!
//! - Commission for the founder (maybe v1)
//! - Decouple from staking (maybe not worth it)
//! - 'rebond'.
//! - Partial unbonding ()
//! - Partial bond-extra
//! - automatic compounding in the pool
//! - Various, configurable joining policies.
//! - Private pools: where only approved accounts can join.

type PoolId = u32;

fn pool_account(pool_id: PoolId) -> T::AccountId;
