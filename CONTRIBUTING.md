# Contributing

Bug reports and pull requests are welcome. For security problems, please follow [`SECURITY.md`](SECURITY.md) instead of opening a public issue.

## Build and test

You need a stable Rust toolchain (the minimum supported version is 1.81) and Python 3.

```sh
cargo fmt --all -- --check
cargo clippy --all-targets -- -D warnings
cargo test --release
cargo check --no-default-features
python3 scripts/crosscheck.py
```

Use `--release` for the tests: some of them run thousands of Miller-Rabin rounds and are slow in debug builds.

To check the WebAssembly build:

```sh
rustup target add wasm32-unknown-unknown
cargo check --target wasm32-unknown-unknown --no-default-features
```

`tests/hygiene.rs` scans the source and docs, and fails on some characters and words (for example em dashes and curly quotes). If it fails, the message names the file and line.

## Lean proofs

The proofs in `lean/DetPrime/` are checked against Mathlib. CI does this on every pull request, so you only need to run it locally if you change a `.lean` file.

1. Install [elan](https://github.com/leanprover/elan).
2. Get Mathlib at the tag CI uses, with its prebuilt cache:

   ```sh
   git clone --depth 1 --branch v4.33.1 https://github.com/leanprover-community/mathlib4
   (cd mathlib4 && lake exe cache get)
   ```

3. Compile, replay, and audit the proofs:

   ```sh
   MATHLIB_DIR=$PWD/mathlib4 ./lean/replay.sh
   ```

See [`PROOF.md`](PROOF.md) for what each module proves.

## Pull requests

- Keep the crate free of runtime dependencies and `unsafe` code.
- Add a test for any bug fix.
- Add a line to the `Unreleased` section of [`CHANGELOG.md`](CHANGELOG.md) for user-visible changes.
