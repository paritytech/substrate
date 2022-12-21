# Migrations submodule

The Migrations submodule implements storage migrations for pallet-stake-tracker.

## Overview

The Migrations submodule depends on pallet-stake-tracker and pallet-staking as it needs access to 
storage of both of these pallets, while avoiding direct dependency from one to another.
