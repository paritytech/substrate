# Child Bounties Pallet (pallet-child-bounties)

## Child Bounty

> NOTE: This pallet is tightly coupled with pallet-treasury and pallet-bounties.

A Child Bounty is a smaller piece of work, extracted from a parent bounty, that needs to be executed for a predefined Treasury amount to be paid out.
A curator is assigned after the child-bounty is created by the parent bounty curator, to be delegated with the responsibility of assigning a payout address once the specified set of tasks is completed.

## Interface

### Dispatchable Functions

- `add_child_bounty` - Add a child-bounty for a parent-bounty to for dividing the work in smaller tasks.
- `propose_curator` - Assign an account to a child-bounty as candidate curator.
- `accept_curator` - Accept a child-bounty assignment from the parent-bounty curator, setting a curator deposit.
- `award_child_bounty` - Close and pay out the specified amount for the completed work.
- `claim_child_bounty` - Claim a specific child-bounty amount from the payout address.
- `unassign_curator` - Unassign an accepted curator from a specific child-bounty.
- `close_child_bounty` - Cancel the child-bounty for a specific treasury amount and close the bounty.
