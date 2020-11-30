# Bounties Module ( pallet-bounties )

## Bounty

**Note :: This pallet is tightly coupled with pallet-treasury**

A Bounty Spending is a reward for a specified body of work - or specified set of objectives - that
needs to be executed for a predefined Treasury amount to be paid out. A curator is assigned after
the bounty is approved and funded by Council, to be delegated with the responsibility of assigning a
payout address once the specified set of objectives is completed.

After the Council has activated a bounty, it delegates the work that requires expertise to a curator
in exchange of a deposit. Once the curator accepts the bounty, they get to close the active bounty.
Closing the active bounty enacts a delayed payout to the payout address, the curator fee and the
return of the curator deposit. The delay allows for intervention through regular democracy. The
Council gets to unassign the curator, resulting in a new curator election. The Council also gets to
cancel the bounty if deemed necessary before assigning a curator or once the bounty is active or
payout is pending, resulting in the slash of the curator's deposit.

### Terminology

- **Bounty spending proposal:** A proposal to reward a predefined body of work upon completion by
  the Treasury.
- **Proposer:** An account proposing a bounty spending.
- **Curator:** An account managing the bounty and assigning a payout address receiving the reward
  for the completion of work.
- **Deposit:** The amount held on deposit for placing a bounty proposal plus the amount held on
  deposit per byte within the bounty description.
- **Curator deposit:** The payment from a candidate willing to curate an approved bounty. The
  deposit is returned when/if the bounty is completed.
- **Bounty value:** The total amount that should be paid to the Payout Address if the bounty is
  rewarded.
- **Payout address:** The account to which the total or part of the bounty is assigned to.
- **Payout Delay:** The delay period for which a bounty beneficiary needs to wait before claiming.
- **Curator fee:** The reserved upfront payment for a curator for work related to the bounty.

## Interface

### Dispatchable Functions

Bounty protocol:
- `propose_bounty` - Propose a specific treasury amount to be earmarked for a predefined set of
  tasks and stake the required deposit.
- `approve_bounty` - Accept a specific treasury amount to be earmarked for a predefined body of
  work.
- `propose_curator` - Assign an account to a bounty as candidate curator.
- `accept_curator` - Accept a bounty assignment from the Council, setting a curator deposit.
- `extend_bounty_expiry` - Extend the expiry block number of the bounty and stay active.
- `award_bounty` - Close and pay out the specified amount for the completed work.
- `claim_bounty` - Claim a specific bounty amount from the Payout Address.
- `unassign_curator` - Unassign an accepted curator from a specific earmark.
- `close_bounty` - Cancel the earmark for a specific treasury amount and close the bounty.
