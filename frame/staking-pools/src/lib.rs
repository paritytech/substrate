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
//! increase their probability of receiving rewards. Recall that the 1st class nominator position is
//! reserved for accounts with the most amount of stake. The relay chain will benefit from staking
//! pools by increasing the total amount of tokens at stake, while still keeping them in the relay
//! chain, usable for governance and other purposes.
//!
//! ## V1 Specification
//!
//! > The staking pool is considered to be an extension that can *only* be used in a chain that
//! > contains the default substrate `pallet-staking`. In the implementation, we will most likely
//! > make it strictly depend on `pallet-staking` as well. We won't consider any decision to make
//! > this particularly _reusable_.
//!
//! #### Pool and the Founder
//!
//! Each pool has a founder that reserves a fixed (and relatively hefty amount of) deposit to
//! created it. The founder will decide which validators the entire pool will eventually nominate.
//! Thus, the same trust relationship that exist between nominators and validators also exists
//! between pool founders and their members. Each pool is associated with a single inaccessible
//! account (pool's "Bonded Account"), derived from the pool identifier. This account is always
//! *fully bonded* (has no unlocked balance), and  will eventually act as the final 'Nominator' that
//! will submit a `nominate` extrinsic on behalf of the entire pool. The pool account is forbidden
//! from ever submitting any other transaction, other than `nominate` and a handful of other
//! well-known operations.
//!
//! Note that a pool is simply a normal nomination from the point of view of the staking pallet, and
//! there is absolutely no guarantee that the pool will become an *exposed* nominator. This is
//! entirely based on:
//!
//! 1. whether the pool has enough collective stake to be part of the election snapshot.
//! 2. whether the mining algorithm includes the pool nominator in the election result.
//!
//! If the pool has sufficiently high amount of collective stake in it, the probability of both of
//! the previous points are very high. If exposed, and if an account triggers the appropriate
//! `payout_stakers`, the pool will receive rewards from the staking system in a secondary account
//! ("Reward Account") that is similarly inaccessible to anyone other than the pool's logic.
//!
//! #### Members and Joining
//!
//! An account joins the pool (and become a "member") by accepting the consequence of putting a lock
//! on their account, which renders a chunk of their balance as unusable for transfers and other
//! purposes. This, in return, mints the equivalent tokens in the pool's bonded account, and
//! immediately triggers a `bond_extra` to the staking pallet. Note that these tokens are not really
//! part of the total issuance and are merely a derivative of the original tokens that is still in
//! the joining member's account.
//!
//! The main purpose of this design over transferring the funds to the pool's bonded account, or
//! reserving them, is to allow the pool members to still use their funds for governance and other
//! lock-based actions, as long as they meet the conditions. This is similar to how stakers of
//! `pallet-staking` only lock their tokens for staking.
//!
//! Recall that all of the rewards go to an *unstaked* account (no compounding), meaning that the
//! *staked* amount of the pool does not automatically change (other than slashing, which we address
//! later). Therefore, the pool can always be in a state where a mapping of each member's *share* of
//! the pool's stake is known. Thus, each member's share of the *rewards being accumulated* (in the
//! reward account) is also known. A period of time during which the this mapping is static, and
//! rewards are being accumulated is called a "payout round", or "round" for short. A round can only
//! end if a "payout_all" function is called, where all of the rewards are payed out, without
//! anyone's share changing. This function can be called by anyone at any time, if they are willing
//! to pay its fees. The payouts are directly transferred to the corresponding member's free
//! balance, thus compounding is not really possible at the pool level.
//!
//! Furthermore, any interaction that disrupts the mapping of shares needs to perform two actions
//! implicitly:
//!
//! 1. `payout_all`, where all leftover payouts are paid.
//! 2. `re_balance_shares`, where all of the shares are re-computed.
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
//! Additionally, to protect against spam themselves, pools can also declare a minimum joining
//! policy. Indeed, for this to make any economic sense, it needs to be less than the threshold
//! needed to become a 1st class nominator.
//!
//! ### Leaving and Slashing
//!
//! First, recall that each account's original contribution to the pool is clear and constant: the
//! pool can always compute this, by looking into the locks of a certain account, and see how much
//! lock it has there. Henceforth, by querying the "original contribution", we mean this process.
//! Note that the staking-pools pallet could potentially store this information internally as well,
//! but it won't be of much extra use.
//!
//! Leaving the pool has exactly the same implications as the staking system does. An intention to
//! leave (called `unbond_all`, which implies partial bonding is not possible) must be submitted by
//! a member, which will trigger an `unbond` to the staking pallet. Upon `unbond_all`, the current
//! era index is recorded for the leaving member. In other words, a record of `(AccountId,
//! EraIndex)` is appended to a `LeavingQueue` storage item.
//!
//! While the leaving member is waiting for their unbonding period, they still receive their reward
//! shares, and are fully exposed to being slashed, unlike pallet-staking. More on this further
//! down.
//!
//! Leaving is a one-way operation with no turning back.
//!
//! At any point in the future, a separate `process_unbonding` transaction can be called. This will
//! trigger a `withdraw_unbonded` under the hood. Consequently, if enough time from any number of
//! `unbond_all` calls have been passed, it will cause a certain amount of tokens to become unlocked
//! in the pool's bonded account. If any amount `X` is now transferrable, where `X > 0`, then the
//! pool needs to lookup all the accounts in the `LeavingQueue` who's leaving era index is more than
//! one full bonding period (e.g. 28 days) old. These accounts are the ones that are now ready to
//! finally leave the pool. The sum of the original contribution of these accounts is compute as
//! `Y`.
//!
//! In all normal cases, in the absence of slashing (any any unforeseen bugs), `X == Y` always holds
//! at this point in time. If so, `X` is burned, and the original contributions are symbolically
//! returned, by removing the balance lock on the original account.
//!
//! If `X > Y`, this must be a logical bug in the pallet. Excess funds (`E = X - Y`) should be moved
//! to an inaccessible "Credit Account" and appropriate governance controls over this account should
//! be provided (e.g. `burn`, or transfer).
//!
//! If `X < Y`, this must mean that the original funds in pallet-staking have been subject to a
//! slash, and the `process_unbonding` operation is rejected. Moreover, this means that the slash
//! must have been enacted after the current leaving accounts submitted `unbond_all`, since
//! otherwise submitting `unbond_all` would have not been possible.
//!
//! Now, we address the last case and wrap up the slashing details of leaving. Recall that the pool
//! is always trying to maintain a state where each member's share of the accumulating rewards are
//! known. A similar property must always be upheld about the initial contributions as well:
//!
//! The sum of all account's contribution, must be equal to the `ledger.active` of the pool's bonded
//! account.
//!
//! This property is checked before any member leaves the pool. If this property is not upheld, then
//! the leaving operation fails, stating that the pool is in "imbalanced-contributions" state, and a
//! re-configuration transaction needs to be submitted to the pool to re-balance it
//! (`re_balance_contributions`). This re-balance operation will look at the slash amount (`S = X -
//! L` where `X` is the sum of contributions and `L` is `ledger.total`), and reduce each member's
//! initial contribution amount pro-rata.
//!
//! A nice property here is that since the slashes are applied pro-rata, it does not change any
//! member's share (the ratio of their contribution, compared to the total stake of the pool) in the
//! pool, meaning that the rewards can still be paid out of the pool's reward account, without the
//! need for a share re-balancing.
//!
//! > Interestingly, as long as the share mapping is untouched, unlike the normal staking pallet,
//! the rewards of the staking pool do not have any expiration date and can be claimed months and
//! years after being accumulated. This, combined with "private pools" could lead to interesting use
//! cases.
//!
//! > The main caveat here is that the pool cannot really know when a slash happened, and therefore
//! > applies it, whenever it is told to via `re_balance_contributions`, to all of its current
//! > members. This can be unfavorable for a few groups of people:
//!
//! 1. Those who joined very recently. This people will be slashed, even if the original slash event
//!    was prior to them joining.
//! 2. Those who called `unbond_all` before the slash happened, but could not leave the pool in time
//!    to avoid the slash. Although, since usually `SlashDeferDuration` is very close to
//!    `BondingDuration`, this is relatively unlikely to happen.
//!
//! The main reason for this is that we should not assume that all pools can be notified of slashes.
//! This will not scale with many many pools. Instead, the pools should spontaneously realize that
//! they have been slashed, and apply it in a best-effort manner.
//!
//! ### Summary
//!
//! To summarize:
//!
//! The pool has the following accounts:
//!
//! 1. Bonded account: where all of the tokens in this account are always bonded. The only way to
//!    add more bonded tokens to this is by new members joining, not via compounding.
//! 2. Reward account: an unbonded account where all the rewards from the pool are accumulated.
//! 3. Credit account: an account to place any excess funds, due to bugs.
//!
//! Important storage items, where all of them are stored per pool (i.e. all of them are maps):
//!
//! 1. `SumContributions`: a value which should always be equal to the `ledger.total` of the bonded
//!    account. Else, the pool must have been slashed, and no member can leave the pool until the
//!    slash is applied.
//! 2. `Shares`: a mapping from each member's share in the pool. For any member, this is simply
//!    their ratio of contribution to the pool, divided by `SumContribution`.
//! 3. LeavingQueue`: A list of members who set the intention to leave, and the era index at which
//!    they did so. This is used for clear accounting when members want to leave.
//!
//! Two important properties exist in a pool:
//!
//! 1. balanced shares: where each member's claim to the accumulating rewards in the "reward
//!    account" is know by looking at their entry in `Shares` Any operation that disrupts this
//!    property needs to payout all the current rewards, and compute the new `Shares`. This is
//!    called `re_balance_shares`.
//! 2. balanced contributions: `SumContributions` is equal to `ledger.total` of the pool's bonded
//!    account. This can only be disrupted by a slash, at which point no member can leave the pool
//!    until it has been re-calculated. This is called `re_balance_contributions`.
//!
//! Typical member operations are:
//!
//! 1. joining: triggers a `payout_all` and `re_balance_shares`.
//! 2. paying out rewards: can be called and need not any re_balancing.
//! 3. leaving: triggers a `payout_all` and `re_balance_shares` at the last step when leavin
//!
//! > A (minor) hassle of this implementation is that we are treating locked currency as
//! *slashable*, while clearly they are not meant for it. This is why manual operations like minting
//! and burning are needed, assuming the current `LockableCurrency` APIs.
//!
//! ### Dissolving
//!
//! TODO
//!
//! ## V2 features:
//!
//! - Commission for the founder (maybe v1)
//! - Decouple from staking (maybe not worth it)
//! - 'rebond' (will likely NEVER be possible with my design)
//! - Partial unbonding (will likely NEVER be possible with my design)
//! - bond-extra ()
//! - automatic compounding in the pool
//! - Various, configurable joining policies.
//! - Private pools: where only approved accounts can join.

type PoolId = u32;

fn pool_account(pool_id: PoolId) -> T::AccountId;
