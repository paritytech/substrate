# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [2.2.3]

### Added

-

### Removed

-

### Changed

- MILLICENTS set to `100_000` to match Network decimals
- MILLISECS_PER_BLOCK set to `6000`
- Fees ratio set to 50%/50%
- Inflation set to `0`
- Burn set to `0`

### Fixed

-

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
