# Initializer submodule

The Initializer submodule implements storage initialization for pallet-stake-tracker.

## Overview

The Initializer submodule depends on pallet-stake-tracker and pallet-staking as it needs access to 
storage of both of these pallets, while avoiding direct dependency from one to another.
