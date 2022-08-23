# Transaction Payment Module

This module provides the basic logic needed to pay the absolute minimum amount needed for a
transaction to be included. This includes:
  - _weight fee_: A fee proportional to amount of weight a transaction consumes.
  - _length fee_: A fee proportional to the encoded length of the transaction.
  - _tip_: An optional tip. Tip increases the priority of the transaction, giving it a higher
    chance to be included by the transaction queue.

Additionally, this module allows one to configure:
  - The mapping between one unit of weight to one unit of fee via [`Config::WeightToFee`].
  - A means of updating the fee for the next block, via defining a multiplier, based on the
    final state of the chain at the end of the previous block. This can be configured via
    [`Config::FeeMultiplierUpdate`]

License: Apache-2.0