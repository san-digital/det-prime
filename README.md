# det-prime

Deterministic, zero-entropy primality testing, transcript-to-prime hashing, primes in arithmetic progressions, and modular square roots for `#![no_std]` Rust and WebAssembly (`wasm32-unknown-unknown`).

Zero runtime dependencies. `#![forbid(unsafe_code)]`. Stack-allocated fixed-width limbs up to 4096 bits. Backed by Lean 4 proofs in [`lean/DetPrime/`](lean/DetPrime) and documented assumption boundaries in [`PROOF.md`](PROOF.md).

## Why This Exists

Standard cryptographic and zero-knowledge libraries use probabilistic Miller-Rabin (`k` random rounds) and randomized Tonelli-Shanks (rejection-sampling a quadratic non-residue). That creates three recurring engineering problems:

1. **Entropy-free execution environments:** `wasm32-unknown-unknown` guests, smart-contract VMs, zkVMs, and consensus state transitions have no OS CSPRNG and require bit-identical execution across validators.
2. **Adversarial parameter validation:** Fixed small-base Miller-Rabin tables fail against constructed strong pseudoprimes (Arnault's 46-digit composite passes all 11 prime bases `2..=31`; Sorenson-Webster's 82-bit composite passes `2..=41`) and Carmichael numbers.
3. **Verifiable delay functions and Fiat-Shamir challenges:** Wesolowski VDF verifiers and RSA accumulator transcripts must map a 256-bit hash digest deterministically to a prime challenge without interactive randomness.

`det-prime` replaces random witness sampling with deterministic prime-base bounds:

- **`n < 2^64` (`is_prime_u64`):** Unconditional 7-base Sinclair witness set (`[2, 325, 9375, 28178, 450775, 9780504, 1795265022]`), exact across all 64-bit integers.
- **`2^64 <= n < 2^4096` (`is_prime`, `verify_miller_bach`):** Tests prime bases `p <= floor(2 * ln_hi(n)^2)` via 4-bit windowed CIOS Montgomery multiplication, returning either a `PrimalityCertificate` or an explicit `CompositeWitness` (`Even`, `PrimeFactor(p)`, or `StrongWitness(p)`).
- **`sqrt_mod_prime` and `least_nonresidue`:** Finds the least prime quadratic non-residue `q <= floor(ln_hi(p)^2)` deterministically and runs Tonelli-Shanks without randomness, returning the canonical root `r <= (p - 1) / 2` after verifying `r^2 == a (mod p)`.
- **`hash_to_prime_256`:** Maps any 32-byte digest deterministically to a 255-bit odd prime along a bounded candidate sequence.
- **`prime_in_progression_u64`:** Finds the smallest prime `p == a (mod q)` within `(phi(q) * ln q)^2` (for example, NTT-friendly primes `p == 1 (mod 2^k)`).

## Usage

```toml
[dependencies]
det-prime = { git = "https://github.com/san-digital/det-prime" }
```

For `#![no_std]` or `wasm32-unknown-unknown` targets:

```toml
[dependencies]
det-prime = { git = "https://github.com/san-digital/det-prime", default-features = false }
```

### Deterministic Primality and Adversarial Witness Extraction

```rust
use det_prime::{is_prime, verify_miller_bach, CompositeWitness, U256};

// secp256k1 field prime: 2^256 - 2^32 - 977
let secp = U256::from_hex(
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
).unwrap();
assert!(is_prime(&secp));
let cert = verify_miller_bach(&secp).unwrap();
assert_eq!(cert.prime_base_bound, 62_973);

// Arnault's 46-digit strong pseudoprime to all 11 prime bases 2..=31:
let arnault = U256::from_decimal(
    "1195068768795265792518361315725116351898245581",
).unwrap();
assert_eq!(
    verify_miller_bach(&arnault),
    Err(CompositeWitness::StrongWitness(37)),
);
```

### Deterministic VDF / Fiat-Shamir Hash-to-Prime

```rust
use det_prime::{hash_to_prime_256, is_prime};

let transcript_digest = [0x42u8; 32];
let (challenge_prime, odd_steps) = hash_to_prime_256(&transcript_digest).unwrap();
assert_eq!(challenge_prime.bits(), 255);
assert!(is_prime(&challenge_prime));
assert!(odd_steps >= 1);
```

### Deterministic Tonelli-Shanks on High 2-Adicity ZK Fields

```rust
use det_prime::{least_nonresidue, sqrt_mod_prime, U256};

// Stark252 prime: p = 2^251 + 17 * 2^192 + 1 (2-adicity 192)
let stark = U256::from_hex(
    "0800000000000011000000000000000000000000000000000000000000000001",
).unwrap();
assert_eq!(least_nonresidue(&stark).unwrap(), 3);

let root = sqrt_mod_prime(&U256::from_u64(9), &stark).unwrap().unwrap();
assert_eq!(root, U256::from_u64(3));
```

## Measured Timings

Single-core `cargo run --release --example timing` on Apple Silicon (M-series, `rustc 1.94.0`):

| Operation | Input | Latency |
| :--- | :--- | :--- |
| `is_prime_u64` | 64-bit odd integers (10,000 calls) | **0.97 us / call** |
| `is_prime` (`U256`) | 256-bit odd composite | **< 0.01 us / call** |
| `is_prime` (`U256`) | 256-bit `secp256k1` prime (all 6,301 prime bases `<= 62,973`) | **36.3 ms** |
| `hash_to_prime_256` | 32-byte digest -> 255-bit prime (108 odd steps) | **30.2 ms** |
| `sqrt_mod_prime` (`U256`) | Stark252 (`2^192 \| p - 1`, deterministic Tonelli-Shanks) | **0.72 ms / call** |
| `prime_in_progression_u64` | `q = 2^20, a = 1` -> `p = 7,340,033` | **1.88 us** |

*Security note:* `det-prime` is built for deterministic verification of public parameters, consensus inputs, curve/field moduli, and public VDF/Fiat-Shamir transcripts. Branching and early exit on composite witnesses are data-dependent; do not use `det-prime` to generate secret RSA key factors where constant-time execution is required.

## Soundness and Lean 4 Verification

`det-prime` splits its mathematical claims into three explicit layers (detailed in [`PROOF.md`](PROOF.md)):

1. **Local Lean 4 proofs (`lean/DetPrime/`, kernel-replayed via `leanchecker` with zero `sorryAx`):**
   - `LogBounds.lean`: Proves the pure-integer `u128` rational bound `ln_upper_scaled` strictly encloses `ln(n)` and that `bach_bound_from_km` and `lls_bound_from_km` enclose `2 * (ln n)^2` and `(ln p)^2`.
   - `PrimeWitness.lean`: Proves subgroup prime-factor witness reduction, Solovay-Strassen properness of the Euler-Jacobi subgroup for all odd composites, Monier-Rabin strong-liar inclusion in the Euler-Jacobi subgroup, and zero false negatives on primes.
   - `TonelliShanks.lean`: Proves prime non-residue reduction, the `p == 3 (mod 4)` branch, and the Tonelli-Shanks loop step invariant.
   - `BridgeAudit.lean`: Composes the local proofs with the analytic bound interfaces into the bidirectional equivalence `miller_bach_prime_iff_all_prime_bases` and `least_nonresidue_has_prime_witness`.
2. **Published explicit analytic bounds:** Bach (1990, Theorem 2), Lamzouri, Li & Soundararajan (2015, Corollaries 1.1 & 1.2), and Carneiro, Milinovich & Soundararajan (2019, Theorem 5).
3. **Upstream zero-free half-plane hypotheses:** `DirichletLNonvanishingRightOfHalf` and `RiemannZetaZerosOnLine` match Levent Alpoge's `Statements.lean` (20 November 2026, kernel-replayed in Lean 4; human peer review ongoing) verbatim. All `u64` operations (`is_prime_u64`) are unconditional.

## Verification

```sh
cargo fmt --all -- --check
cargo clippy --all-targets -- -D warnings
RUSTFLAGS="-D warnings" cargo test --release
RUSTFLAGS="-D warnings" cargo check --no-default-features
RUSTFLAGS="-D warnings" cargo check --target wasm32-unknown-unknown --no-default-features
python3 scripts/crosscheck.py
```

To replay the Lean 4 modules against a compiled Mathlib4 workspace:

```sh
MATHLIB_DIR=/path/to/mathlib4 ./lean/replay.sh
```

## License

Apache-2.0. See [`LICENSE`](LICENSE).
