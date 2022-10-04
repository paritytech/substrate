# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [2.23.0]
### Changed
- Updated Substrate to polkadot-v0.9.9

## [2.22.0]
### Changed
- Updated Substrate to polkadot-v0.9.8

## [2.21.0]
### Changed
- Updated Substrate to polkadot-v0.9.5

## [2.20.0]
### Changed
- Updated Substrate to polkadot-v0.9.4

## [2.20.0]
### Changed
- Updated Substrate to polkadot-v0.9.3

## [2.19.0]
### Changed
- Updated Substrate to polkadot-v0.9.2

## [2.18.0]
### Changed
- Updated Substrate to polkadot-v0.9.1

## [2.17.0]
### Changed
- Updated Substrate to polkadot-v0.9.0

## [2.16.0]
### Changed
- Updated Substrate to polkadot-v0.8.30

## [2.15.0]
### Changed
- Updated Substrate to polkadot-v0.8.29

## [2.14.0]
### Changed
- Updated Substrate to polkadot-v0.8.28

## [2.13.0]
### Changed
- Updated Substrate to polkadot-v0.8.27

## [2.12.0]
### Changed
- Updated Substrate to polkadot-v0.8.26

## [2.11.0]
### Changed
- Updated Substrate to polkadot-v0.8.25
- Minor fixes performed and tests updated

## [2.10.0]
### Changed
- Updated inflation parameters

## [2.9.0]
### Changed
- Enabled native transfer on erc20 frame

## [2.8.0]
### Changed
- Enabled inflation

## [2.7.0]
### Changed
- Bonding period set to 3 eras, SlashDeferDuration set to 2 eras

## [2.6.0]
### Changed

- Democracy's Launch/Voting/Enactment periods set to 1 day
- Democracy's Minimum Deposit set to 5000 dollars

## [2.5.1]

### Fixed

- DDC Metrics OCW compatibility with DDC SC

## [2.5.0]

### Changed

- Added dynamic block interval
- Added validation for resource Id in chainbridge frame.
- Set democracy periods: `LaunchPeriod` to 1 day, `VotingPeriod` to 5 days, `EnactmentPeriod` to 3 days.
- Updated `FastTrackVotingPeriod` to 3 hours.
- Updated nightly version to 2021-05-21
- Added script to extract wasm file.

## [2.3.2]

### Changed

- Added CI/CD scripts for E2E testing of OCW + DDC_SC + DDC_NODE
- Removed Node-Template runtime
- Removed hardcoded SC address configuration from runtime
- Added DDN status reporting
- Added DDN metrics
- Added period finalization call
- Updated tests

## [2.3.1]

### Changed

- EnactmentPeriod set to 28 DAYS
- CooloffPeriod set to 7 DAYS
- BondingDuration set to 28 DAYS
- SlashDeferDuration set to 27 DAYS
- MaxNominatorRewardedPerValidator set to 256
- IndexDeposit set to 10 DOLLARS
- UncleGenerations set to 0
- CouncilMotionDuration set to 7 DAYS
- CandidacyBond set to 100 DOLLARS
- DesiredRunnersUp set to 20
- ProposalBondMinimum set to 100 DOLLARS
- BountyDepositPayoutDelay set to 8 DAYS
- BountyUpdatePeriod set to 90 DAYS
- BountyValueMinimum set to 10 DOLLARS
- MinVestedTransfer set to 1 DOLLAR

## [2.3.0]

### Added

- DDC Metrics reporter using offchain worker

## [2.2.4]

### Changed

- EPOCH_DURATION_IN_BLOCKS set to 4 HOURS

## [2.2.3]

### Changed

- MILLICENTS set to `100_000` to match Network decimals
- MILLISECS_PER_BLOCK set to `6000`
- Fees ratio set to 50%/50%
- Inflation set to `0`
- Burn set to `0`

## [2.2.2]

### Added

-

### Removed

- transfer_native function in erc20 frame

### Changed

-

### Fixed

-

## [2.2.1]

### Added

-

### Removed

-

### Changed

-

### Fixed

- Reverted ChainBridge's runtime changes
- Use nightly-2021-05-07

## [2.2.0] - 2021-04-16

### Added

- Added 3 new pallets for ERC20 integration. Source is [here](https://github.com/ChainSafe/chainbridge-substrate):
	- pallet-chainbridge
	- pallet-erc721
	- pallet-erc20

### Removed

-

### Changed

-

### Fixed

-

## [2.1.0-rc2] - 2021-03-26

### Changed

- Use rust `nightly` for build and tests running

## [2.1.0-rc1] - 2021-03-25

### Added

- Integrate DDC pallet
- Add Github actions for Node image build and tests run

### Changed

- Rename executable file
- Update README file

[2.1.0-rc2]: https://github.com/Cerebellum-Network/pos-network-node/compare/v2.1.0-rc2...v2.1.0-rc1
[2.1.0-rc1]: https://github.com/Cerebellum-Network/pos-network-node/compare/v2.1.0-rc1...v2.0.1
