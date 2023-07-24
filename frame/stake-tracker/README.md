# Pallet `stake-tracker`

The stake-tracker pallet is listens to staking events and forwards those events to one or
multiple types (e.g. pallets). It works as a multiplexer of staking events and it is used to
update semi-sorted target and voter lists implemented with bags lists.
 
