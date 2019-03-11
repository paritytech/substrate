# Timestamp Module

The timestamp module provides functionality to get and set the on-chain time.

## Overview

The timestamp module allows the validators to set and validate a timestamp with each block. It uses timestamp data as an inherent which is provided by the block author and validated/verified by other validators.

It is expected that the timestamp is set by the validator in the beginning of each block, typically one of the first extrinsics. The timestamp can be set only once per block and must be set each block.

Note, that there might be a constraint on how much time must pass before setting the new timestamp, specified by the `tim:block_period` storage entry.

The timestamp module is the recommended way to query the on-chain time instead of using an approach based on block numbers. The block numbers based time measurement can cause issues because of cummulative calculation errors and hence it should be avoided.

## Public Interface

### Types

* `Moment` - Represents the current timestamp.

### Storage Items

* `Now`: `Moment` - The current timestamp represented as **total seconds from the unix epoch**.
* `BlockPeriod`: `Moment` - The minimum (and advised) period between blocks.

### Public Immutable functions

#### get()

Get the current time for the current block. If this function is called prior the setting to timestamp, it will return the timestamp of the previous block.

Returns the timestamp as `Moment`.

#### block_period()

Get the block period for the chain. Return the block period as the `Moment` type.

### Public Mutable functions

#### set(origin, now: T::Moment)

Sets the current time. This call should be invoked exactly once per block. It will panic at the finalization phase, if this call hasn't been invoked by that time.

The timestamp should be greater than the previous one by the amount specified by `block_period`.

##### Errors:

* Timestamp must be updated only once in the block
* Timestamp must increment by at least `BlockPeriod` between sequential blocks

### Inherent Data

The timestamp module manages the block timestamp using InherentData. To identify the timestamp inherent, it defines an `InherentIdentifier`.

The timestamp module defines and implements the trait `TimestampInherentData` for `InherentData` to query the timestamp inherent using the timestamp `InherentIdentifier`.

## Usage

The following example shows how to use the timestamp module in your custom module to query the current timestamp.

In your custom module, after importing the `timestamp` module and deriving your module's configuration trait with the timestamp trait, call the timestamp module's `get` function to get the current timestamp,

```
let now = <timestamp::Module<T>>::get();
```

Similarly, the `block_period` function can be called.