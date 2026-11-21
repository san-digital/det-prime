# Changelog

All notable changes to this project are listed here. The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project uses [Semantic Versioning](https://semver.org/).

## [Unreleased]

### Changed

- The README, crate docs, `PROOF.md`, and the crates.io description now state plainly that results for `n >= 2^64` are correct assuming GRH, and that `u64` results are unconditional. The README was rewritten to be shorter and to lead with installation and an example.
- Corrected two numbers in the docs: the secp256k1 test tries 6,316 prime bases (not 6,301), and `2 * (ln 2^4096)^2` is about 16,121,328 (not 16,121,365).
- The published crate no longer includes CI configuration or the Python cross-check script.

### Added

- `CHANGELOG.md`, `CONTRIBUTING.md`, and `SECURITY.md`.
- A CI job that builds and tests on the minimum supported Rust version (1.81).

## [0.1.1] - 2026-11-21

### Fixed

- `hash_to_prime_256` could return a 256-bit prime (for example `2^255 + 95` for an all-`0xff` digest) when the start point was above the largest prime below `2^255`. The scan now wraps to `2^254 + 1`. Every other digest maps to the same prime as before.
- `prime_in_progression_u64` returned `Err(Overflow)` for `q` above about `2^59`, even though the scan is capped at `u64::MAX`.

### Changed

- Documented that `sqrt_mod_prime` requires a prime modulus, that it is limited to 4096 bits, and that `is_prime` returns `false` without testing for `n >= 2^4096`.
- CI now replays the Lean proofs, and the axiom audit only accepts `propext`, `Classical.choice`, and `Quot.sound`.
- Corrected the journal for the Carneiro, Milinovich and Soundararajan citation.

## [0.1.0] - 2026-11-21

Initial release.

[Unreleased]: https://github.com/san-digital/det-prime/compare/v0.1.1...HEAD
[0.1.1]: https://github.com/san-digital/det-prime/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/san-digital/det-prime/releases/tag/v0.1.0
