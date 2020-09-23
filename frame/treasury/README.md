# Treasury Module

The Treasury module provides a "pot" of funds that can be managed by stakeholders in the
system and a structure for making spending proposals from this pot.

- [`treasury::Trait`](https://docs.rs/pallet-treasury/latest/pallet_treasury/trait.Trait.html)
- [`Call`](https://docs.rs/pallet-treasury/latest/pallet_treasury/enum.Call.html)

## Overview

The Treasury Module itself provides the pot to store funds, and a means for stakeholders to
propose, approve, and deny expenditures. The chain will need to provide a method (e.g.
inflation, fees) for collecting funds.

By way of example, the Council could vote to fund the Treasury with a portion of the block
reward and use the funds to pay developers.

### Tipping

A separate subsystem exists to allow for an agile "tipping" process, whereby a reward may be
given without first having a pre-determined stakeholder group come to consensus on how much
should be paid.

A group of `Tippers` is determined through the config `Trait`. After half of these have declared
some amount that they believe a particular reported reason deserves, then a countdown period is
entered where any remaining members can declare their tip amounts also. After the close of the
countdown period, the median of all declared tips is paid to the reported beneficiary, along
with any finders fee, in case of a public (and bonded) original report.

### Bounty

A Bounty Spending is a reward for a specified body of work - or specified set of objectives - that
needs to be executed for a predefined Treasury amount to be paid out. A curator is assigned after
the bounty is approved and funded by Council, to be delegated
with the responsibility of assigning a payout address once the specified set of objectives is completed.

After the Council has activated a bounty, it delegates the work that requires expertise to a curator
in exchange of a deposit. Once the curator accepts the bounty, they
get to close the Active bounty. Closing the Active bounty enacts a delayed payout to the payout
address, the curator fee and the return of the curator deposit. The
delay allows for intervention through regular democracy. The Council gets to unassign the curator,
resulting in a new curator election. The Council also gets to cancel
the bounty if deemed necessary before assigning a curator or once the bounty is active or payout
is pending, resulting in the slash of the curator's deposit.


### Terminology

- **Proposal:** A suggestion to allocate funds from the pot to a beneficiary.
- **Beneficiary:** An account who will receive the funds from a proposal iff
the proposal is approved.
- **Deposit:** Funds that a proposer must lock when making a proposal. The
deposit will be returned or slashed if the proposal is approved or rejected
respectively.
- **Pot:** Unspent funds accumulated by the treasury module.

Tipping protocol:
- **Tipping:** The process of gathering declarations of amounts to tip and taking the median
  amount to be transferred from the treasury to a beneficiary account.
- **Tip Reason:** The reason for a tip; generally a URL which embodies or explains why a
  particular individual (identified by an account ID) is worthy of a recognition by the
  treasury.
- **Finder:** The original public reporter of some reason for tipping.
- **Finders Fee:** Some proportion of the tip amount that is paid to the reporter of the tip,
  rather than the main beneficiary.

Bounty:
- **Bounty spending proposal:** A proposal to reward a predefined body of work upon completion by
the Treasury.
- **Proposer:** An account proposing a bounty spending.
- **Curator:** An account managing the bounty and assigning a payout address receiving the reward
for the completion of work.
- **Deposit:** The amount held on deposit for placing a bounty proposal plus the amount held on
deposit per byte within the bounty description.
- **Curator deposit:** The payment from a candidate willing to curate an approved bounty. The deposit
is returned when/if the bounty is completed.
- **Bounty value:** The total amount that should be paid to the Payout Address if the bounty is
rewarded.
- **Payout address:** The account to which the total or part of the bounty is assigned to.
- **Payout Delay:** The delay period for which a bounty beneficiary needs to wait before claiming.
- **Curator fee:** The reserved upfront payment for a curator for work related to the bounty.

## Interface

### Dispatchable Functions

General spending/proposal protocol:
- `propose_spend` - Make a spending proposal and stake the required deposit.
- `set_pot` - Set the spendable balance of funds.
- `configure` - Configure the module's proposal requirements.
- `reject_proposal` - Reject a proposal, slashing the deposit.
- `approve_proposal` - Accept the proposal, returning the deposit.

Tipping protocol:
- `report_awesome` - Report something worthy of a tip and register for a finders fee.
- `retract_tip` - Retract a previous (finders fee registered) report.
- `tip_new` - Report an item worthy of a tip and declare a specific amount to tip.
- `tip` - Declare or redeclare an amount to tip for a particular reason.
- `close_tip` - Close and pay out a tip.

Bounty protocol:
- `propose_bounty` - Propose a specific treasury amount to be earmarked for a predefined set of
tasks and stake the required deposit.
- `approve_bounty` - Accept a specific treasury amount to be earmarked for a predefined body of work.
- `propose_curator` - Assign an account to a bounty as candidate curator.
- `accept_curator` - Accept a bounty assignment from the Council, setting a curator deposit.
- `extend_bounty_expiry` - Extend the expiry block number of the bounty and stay active.
- `award_bounty` - Close and pay out the specified amount for the completed work.
- `claim_bounty` - Claim a specific bounty amount from the Payout Address.
- `unassign_curator` - Unassign an accepted curator from a specific earmark.
- `close_bounty` - Cancel the earmark for a specific treasury amount and close the bounty.


## GenesisConfig

The Treasury module depends on the [`GenesisConfig`](https://docs.rs/pallet-treasury/latest/pallet_treasury/struct.GenesisConfig.html).

License: Apache-2.0