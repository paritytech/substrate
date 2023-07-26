# Pallet `stake-tracker`

The stake-tracker pallet is listens to staking events through implemeting the
[`OnStakingUpdate`] trait and forwards those events to one or multiple types (e.g. pallets) that
must be kept up to date with certain updates in staking. The pallet does not expose any
callables and acts as a multiplexer of staking events.

 Currently, the stake tracker pallet is used to update the semi-sorted target and voter lists
 implemented through bags lists.
