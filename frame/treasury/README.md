# Treasury Module

The Treasury module provides a "pot" of funds that can be managed by stakeholders in the system and
a structure for making spending proposals from this pot.

## Overview

The Treasury Module itself provides the pot to store funds, and a means for stakeholders to propose,
approve, and deny expenditures. The chain will need to provide a method (e.g.inflation, fees) for
collecting funds.

By way of example, the Council could vote to fund the Treasury with a portion of the block reward
and use the funds to pay developers.

### Terminology

- **Proposal:** A suggestion to allocate funds from the pot to a beneficiary.
- **Beneficiary:** An account who will receive the funds from a proposal if the proposal is
  approved.
- **Deposit:** Funds that a proposer must lock when making a proposal. The deposit will be returned
  or slashed if the proposal is approved or rejected respectively.
- **Pot:** Unspent funds accumulated by the treasury module.

## Interface

### Dispatchable Functions

General spending/proposal protocol:
- `propose_spend` - Make a spending proposal and stake the required deposit.
- `reject_proposal` - Reject a proposal, slashing the deposit.
- `approve_proposal` - Accept the proposal, returning the deposit.
