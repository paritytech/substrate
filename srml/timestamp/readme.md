# Timestamp Module

The timestamp module provides functionality to get and set the on-chain time.

## Overview

The timestamp module allows the validators to set and validate a timestamp with each block. It uses timestamp data as inherent data which is provided by the block author and validated/verified by other validators.

The timestamp module is the recommended way to query the on-chain time instead of using an approach based on block numbers. The block numbers based time measurement can cause issues because of cummulative calculation errors and hence it should be avoided.

## Public Interface

### Supported origins

* `inherent` - Used to set the timestamp for the current block

### Types

* `Moment` - Represents the current timestamp. Generally implemented as a `u64`.

### Storage Items

* `Now`: `Moment` - The current timestamp. A `u64` having the timestamps as **total seconds from the unix epoch**.
* `BlockPeriod`: `Moment` - The minimum (and advised) period between blocks. Also represented as `Moment`.
* `DidUpdate`: `bool` - Private flag to check if the timestamp was updated for the current block.

### Public Inspection functions - Immutable (getters)

#### get()

Get the current time for the current block. If this function is called prior the setting the timestamp, it will return the timestamp of the previous block.

Returns the timestamp as `Moment`.

### Public Mutable functions (changing state)

#### set(origin, now: T::Moment)

Sets the current time. Extrinsic with this call should be placed at the specific position in the each block (specified by the Trait::TIMESTAMP_SET_POSITION) typically at the start of the each block. This call should be invoked exactly once per block. It will panic at the finalization phase, if this call hasn't been invoked by that time. 
The timestamp should be greater than the previous one by the amount specified by `block_period`.

##### Errors:

* Timestamp must be updated only once in the block
* Timestamp must increment by at least <BlockPeriod> between sequential blocks

### Inherent Data

The timestamp module manages the block timestamp using InherentData. To identify the timestamp inherent, it defines an `InherentIdentifier`.

The timestamp module defines and implements the trait `TimestampInherentData` for `InherentData` to query the timestamp inherent using the timestamp `InherentIdentifier`.

## Usage

The following example show how to use the timestamp module in your custom module to query the current timestamp.

1. Import the `timestamp` module and derive your module configuration trait with the timestamp trait.

```
use {timestamp};

pub trait Trait: timestamp::Trait { }
```

2. In your module call the timestamp module's get function to get the current timestamp,

```
let now = <timestamp::Module<T>>::get();
```

## Implementation Details

### Module configuration trait

The module configuration trait of the timestamp module derives from the system module and it defines the `Moment` type to represent a timestamp.

### Other implemented traits

As mentioned above, the timestamp module manages the block timestamp using InherentData. To use InherentData, the timestamp module implements the `ProvideInherentData` trait to store the current system time (in seconds).

It also implements the `ProvideInherent` trait to allow the validators to set and validate the timestamp inherent.