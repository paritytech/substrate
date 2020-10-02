# Society Module

- [`society::Trait`](https://docs.rs/pallet-society/latest/pallet_society/trait.Trait.html)
- [`Call`](https://docs.rs/pallet-society/latest/pallet_society/enum.Call.html)

## Overview

The Society module is an economic game which incentivizes users to participate
and maintain a membership society.

### User Types

At any point, a user in the society can be one of a:
* Bidder - A user who has submitted intention of joining the society.
* Candidate - A user who will be voted on to join the society.
* Suspended Candidate - A user who failed to win a vote.
* Member - A user who is a member of the society.
* Suspended Member - A member of the society who has accumulated too many strikes
or failed their membership challenge.

Of the non-suspended members, there is always a:
* Head - A member who is exempt from suspension.
* Defender - A member whose membership is under question and voted on again.

Of the non-suspended members of the society, a random set of them are chosen as
"skeptics". The mechanics of skeptics is explained in the
[member phase](#member-phase) below.

### Mechanics

#### Rewards

Members are incentivized to participate in the society through rewards paid
by the Society treasury. These payments have a maturity period that the user
must wait before they are able to access the funds.

#### Punishments

Members can be punished by slashing the reward payouts that have not been
collected. Additionally, members can accumulate "strikes", and when they
reach a max strike limit, they become suspended.

#### Skeptics

During the voting period, a random set of members are selected as "skeptics".
These skeptics are expected to vote on the current candidates. If they do not vote,
their skeptic status is treated as a rejection vote, the member is deemed
"lazy", and are given a strike per missing vote.

#### Membership Challenges

Every challenge rotation period, an existing member will be randomly selected
to defend their membership into society. Then, other members can vote whether
this defender should stay in society. A simple majority wins vote will determine
the outcome of the user. Ties are treated as a failure of the challenge, but
assuming no one else votes, the defender always get a free vote on their
own challenge keeping them in the society. The Head member is exempt from the
negative outcome of a membership challenge.

#### Society Treasury

The membership society is independently funded by a treasury managed by this
module. Some subset of this treasury is placed in a Society Pot, which is used
to determine the number of accepted bids.

#### Rate of Growth

The membership society can grow at a rate of 10 accepted candidates per rotation period up
to the max membership threshold. Once this threshold is met, candidate selections
are stalled until there is space for new members to join. This can be resolved by
voting out existing members through the random challenges or by using governance
to increase the maximum membership count.

### User Life Cycle

A user can go through the following phases:

```rust
          +------->  User  <----------+
          |           +               |
          |           |               |
+----------------------------------------------+
|         |           |               |        |
|         |           v               |        |
|         |        Bidder <-----------+        |
|         |           +               |        |
|         |           |               +        |
|         |           v            Suspended   |
|         |       Candidate +----> Candidate   |
|         |           +               +        |
|         |           |               |        |
|         +           |               |        |
|   Suspended +------>|               |        |
|      Member         |               |        |
|         ^           |               |        |
|         |           v               |        |
|         +-------+ Member <----------+        |
|                                              |
|                                              |
+------------------Society---------------------+
```

#### Initialization

The society is initialized with a single member who is automatically chosen as the Head.

#### Bid Phase

New users must have a bid to join the society.

A user can make a bid by reserving a deposit. Alternatively, an already existing member
can create a bid on a user's behalf by "vouching" for them.

A bid includes reward information that the user would like to receive for joining
the society. A vouching bid can additionally request some portion of that reward as a tip
to the voucher for vouching for the prospective candidate.

Every rotation period, Bids are ordered by reward amount, and the module
selects as many bids the Society Pot can support for that period.

These selected bids become candidates and move on to the Candidate phase.
Bids that were not selected stay in the bidder pool until they are selected or
a user chooses to "unbid".

#### Candidate Phase

Once a bidder becomes a candidate, members vote whether to approve or reject
that candidate into society. This voting process also happens during a rotation period.

The approval and rejection criteria for candidates are not set on chain,
and may change for different societies.

At the end of the rotation period, we collect the votes for a candidate
and randomly select a vote as the final outcome.

```rust
 [ a-accept, r-reject, s-skeptic ]
+----------------------------------+
|                                  |
|  Member   |0|1|2|3|4|5|6|7|8|9|  |
|  -----------------------------   |
|  Vote     |a|a|a|r|s|r|a|a|s|a|  |
|  -----------------------------   |
|  Selected | | | |x| | | | | | |  |
|                                  |
+----------------------------------+

Result: Rejected
```

Each member that voted opposite to this randomly selected vote is punished by
slashing their unclaimed payouts and increasing the number of strikes they have.

These slashed funds are given to a random user who voted the same as the
selected vote as a reward for participating in the vote.

If the candidate wins the vote, they receive their bid reward as a future payout.
If the bid was placed by a voucher, they will receive their portion of the reward,
before the rest is paid to the winning candidate.

One winning candidate is selected as the Head of the members. This is randomly
chosen, weighted by the number of approvals the winning candidates accumulated.

If the candidate loses the vote, they are suspended and it is up to the Suspension
Judgement origin to determine if the candidate should go through the bidding process
again, should be accepted into the membership society, or rejected and their deposit
slashed.

#### Member Phase

Once a candidate becomes a member, their role is to participate in society.

Regular participation involves voting on candidates who want to join the membership
society, and by voting in the right way, a member will accumulate future payouts.
When a payout matures, members are able to claim those payouts.

Members can also vouch for users to join the society, and request a "tip" from
the fees the new member would collect by joining the society. This vouching
process is useful in situations where a user may not have enough balance to
satisfy the bid deposit. A member can only vouch one user at a time.

During rotation periods, a random group of members are selected as "skeptics".
These skeptics are expected to vote on the current candidates. If they do not vote,
their skeptic status is treated as a rejection vote, the member is deemed
"lazy", and are given a strike per missing vote.

There is a challenge period in parallel to the rotation period. During a challenge period,
a random member is selected to defend their membership to the society. Other members
make a traditional majority-wins vote to determine if the member should stay in the society.
Ties are treated as a failure of the challenge.

If a member accumulates too many strikes or fails their membership challenge,
they will become suspended. While a member is suspended, they are unable to
claim matured payouts. It is up to the Suspension Judgement origin to determine
if the member should re-enter society or be removed from society with all their
future payouts slashed.

## Interface

### Dispatchable Functions

#### For General Users

* `bid` - A user can make a bid to join the membership society by reserving a deposit.
* `unbid` - A user can withdraw their bid for entry, the deposit is returned.

#### For Members

* `vouch` - A member can place a bid on behalf of a user to join the membership society.
* `unvouch` - A member can revoke their vouch for a user.
* `vote` - A member can vote to approve or reject a candidate's request to join the society.
* `defender_vote` - A member can vote to approve or reject a defender's continued membership
to the society.
* `payout` - A member can claim their first matured payment.
* `unfound` - Allow the founder to unfound the society when they are the only member.

#### For Super Users

* `found` - The founder origin can initiate this society. Useful for bootstrapping the Society
pallet on an already running chain.
* `judge_suspended_member` - The suspension judgement origin is able to make
judgement on a suspended member.
* `judge_suspended_candidate` - The suspension judgement origin is able to
make judgement on a suspended candidate.
* `set_max_membership` - The ROOT origin can update the maximum member count for the society.
The max membership count must be greater than 1.

License: Apache-2.0