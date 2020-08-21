# Treasury Module

The Treasury module provides a "pot" of funds that can be managed by stakeholders in the
system and a structure for making spending proposals from this pot.

- [`treasury::Trait`](./trait.Trait.html)
- [`Call`](./enum.Call.html)

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

## GenesisConfig

The Treasury module depends on the [`GenesisConfig`](./struct.GenesisConfig.html).

License: Apache-2.0