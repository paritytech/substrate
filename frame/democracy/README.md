# Democracy Pallet

- [`democracy::Trait`](https://docs.rs/pallet-democracy/latest/pallet_democracy/trait.Trait.html)
- [`Call`](https://docs.rs/pallet-democracy/latest/pallet_democracy/enum.Call.html)

## Overview

The Democracy pallet handles the administration of general stakeholder voting.

There are two different queues that a proposal can be added to before it
becomes a referendum, 1) the proposal queue consisting of all public proposals
and 2) the external queue consisting of a single proposal that originates
from one of the _external_ origins (such as a collective group).

Every launch period - a length defined in the runtime - the Democracy pallet
launches a referendum from a proposal that it takes from either the proposal
queue or the external queue in turn. Any token holder in the system can vote
on referenda. The voting system
uses time-lock voting by allowing the token holder to set their _conviction_
behind a vote. The conviction will dictate the length of time the tokens
will be locked, as well as the multiplier that scales the vote power.

### Terminology

- **Enactment Period:** The minimum period of locking and the period between a proposal being
approved and enacted.
- **Lock Period:** A period of time after proposal enactment that the tokens of _winning_ voters
will be locked.
- **Conviction:** An indication of a voter's strength of belief in their vote. An increase
of one in conviction indicates that a token holder is willing to lock their tokens for twice
as many lock periods after enactment.
- **Vote:** A value that can either be in approval ("Aye") or rejection ("Nay")
  of a particular referendum.
- **Proposal:** A submission to the chain that represents an action that a proposer (either an
account or an external origin) suggests that the system adopt.
- **Referendum:** A proposal that is in the process of being voted on for
  either acceptance or rejection as a change to the system.
- **Delegation:** The act of granting your voting power to the decisions of another account for
  up to a certain conviction.

### Adaptive Quorum Biasing

A _referendum_ can be either simple majority-carries in which 50%+1 of the
votes decide the outcome or _adaptive quorum biased_. Adaptive quorum biasing
makes the threshold for passing or rejecting a referendum higher or lower
depending on how the referendum was originally proposed. There are two types of
adaptive quorum biasing: 1) _positive turnout bias_ makes a referendum
require a super-majority to pass that decreases as turnout increases and
2) _negative turnout bias_ makes a referendum require a super-majority to
reject that decreases as turnout increases. Another way to think about the
quorum biasing is that _positive bias_ referendums will be rejected by
default and _negative bias_ referendums get passed by default.

## Interface

### Dispatchable Functions

#### Public

These calls can be made from any externally held account capable of creating
a signed extrinsic.

Basic actions:
- `propose` - Submits a sensitive action, represented as a hash. Requires a deposit.
- `second` - Signals agreement with a proposal, moves it higher on the proposal queue, and
  requires a matching deposit to the original.
- `vote` - Votes in a referendum, either the vote is "Aye" to enact the proposal or "Nay" to
  keep the status quo.
- `unvote` - Cancel a previous vote, this must be done by the voter before the vote ends.
- `delegate` - Delegates the voting power (tokens * conviction) to another account.
- `undelegate` - Stops the delegation of voting power to another account.

Administration actions that can be done to any account:
- `reap_vote` - Remove some account's expired votes.
- `unlock` - Redetermine the account's balance lock, potentially making tokens available.

Preimage actions:
- `note_preimage` - Registers the preimage for an upcoming proposal, requires
  a deposit that is returned once the proposal is enacted.
- `note_preimage_operational` - same but provided by `T::OperationalPreimageOrigin`.
- `note_imminent_preimage` - Registers the preimage for an upcoming proposal.
  Does not require a deposit, but the proposal must be in the dispatch queue.
- `note_imminent_preimage_operational` - same but provided by `T::OperationalPreimageOrigin`.
- `reap_preimage` - Removes the preimage for an expired proposal. Will only
  work under the condition that it's the same account that noted it and
  after the voting period, OR it's a different account after the enactment period.

#### Cancellation Origin

This call can only be made by the `CancellationOrigin`.

- `emergency_cancel` - Schedules an emergency cancellation of a referendum.
  Can only happen once to a specific referendum.

#### ExternalOrigin

This call can only be made by the `ExternalOrigin`.

- `external_propose` - Schedules a proposal to become a referendum once it is is legal
  for an externally proposed referendum.

#### External Majority Origin

This call can only be made by the `ExternalMajorityOrigin`.

- `external_propose_majority` - Schedules a proposal to become a majority-carries
	 referendum once it is legal for an externally proposed referendum.

#### External Default Origin

This call can only be made by the `ExternalDefaultOrigin`.

- `external_propose_default` - Schedules a proposal to become a negative-turnout-bias
  referendum once it is legal for an externally proposed referendum.

#### Fast Track Origin

This call can only be made by the `FastTrackOrigin`.

- `fast_track` - Schedules the current externally proposed proposal that
  is "majority-carries" to become a referendum immediately.

#### Veto Origin

This call can only be made by the `VetoOrigin`.

- `veto_external` - Vetoes and blacklists the external proposal hash.

#### Root

- `cancel_referendum` - Removes a referendum.
- `cancel_queued` - Cancels a proposal that is queued for enactment.
- `clear_public_proposal` - Removes all public proposals.

License: Apache-2.0
