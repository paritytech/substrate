# Changelog
All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this crate adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [5.0.0] - UNRELEASED

### Added

### Changed
Generalized the pallet to use `NposSolver` instead of hard coding the phragmen algorithm; Changed the name of the pallet from `pallet-elections-phragmen` to `pallet-elections`

### Fixed

### Security

## [4.0.0] - UNRELEASED

### Added

### Changed
\[**Needs Migration**\] [migrate pallet-elections-phragmen to attribute macros](https://github.com/paritytech/substrate/pull/8044)

### Fixed

### Security

## [3.0.0]

### Added
[Add slashing events to elections-phragmen](https://github.com/paritytech/substrate/pull/7543)

### Changed

### Fixed
[Don't slash all outgoing members](https://github.com/paritytech/substrate/pull/7394)
[Fix wrong outgoing calculation in election](https://github.com/paritytech/substrate/pull/7384)

### Security
\[**Needs Migration**\] [Fix elections-phragmen and proxy issue + Record deposits on-chain](https://github.com/paritytech/substrate/pull/7040)

## [2.0.0] - 2020-09-2020

Initial version from which version tracking has begun.

