# det-prime

[![crates.io](https://img.shields.io/crates/v/det-prime.svg)](https://crates.io/crates/det-prime)
[![docs.rs](https://img.shields.io/docsrs/det-prime)](https://docs.rs/det-prime)
[![CI](https://github.com/san-digital/det-prime/actions/workflows/ci.yml/badge.svg)](https://github.com/san-digital/det-prime/actions/workflows/ci.yml)

det-prime tells you whether a number is prime without using any randomness, so the same input gives the same answer on every machine. It also computes square roots modulo a prime, maps a hash to a prime, and finds primes in arithmetic progressions.

It is meant for Rust code that has no random number source, or where every node must agree on the result: WebAssembly guests, blockchain and zkVM code, and checks on public parameters such as curve moduli. It is `#![no_std]`, has no dependencies and no `unsafe`, and works on stack-allocated integers up to 4096 bits.

## Install

```toml
[dependencies]
det-prime = "0.1"
```

For `no_std` or `wasm32-unknown-unknown`, turn off the default `std` feature:

```toml
[dependencies]
det-prime = { version = "0.1", default-features = false }
```

## Example

```rust
use det_prime::{hash_to_prime_256, is_prime, is_prime_u64, sqrt_mod_prime, U256};

// 64-bit numbers.
assert!(is_prime_u64(18_446_744_073_709_551_557)); // largest prime below 2^64
assert!(!is_prime_u64(3_825_123_056_546_413_051)); // passes Miller-Rabin for bases 2..=31

// Larger numbers use fixed-width types: U128, U256, ..., U4096.
let p = U256::from_hex(
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", // secp256k1 field prime
).unwrap();
assert!(is_prime(&p));

// Square root of 9 modulo p.
assert_eq!(sqrt_mod_prime(&U256::from_u64(9), &p).unwrap(), Some(U256::from_u64(3)));

// Map a 32-byte hash to a 255-bit prime.
let (prime, _candidates_tried) = hash_to_prime_256(&[0x42; 32]).unwrap();
assert_eq!(prime.bits(), 255);
```

[`verify_miller_bach`](https://docs.rs/det-prime/latest/det_prime/fn.verify_miller_bach.html) does the same test as `is_prime` but tells you why a number is composite. Here it catches a number built to fool Miller-Rabin with every prime base up to 31:

```rust
use det_prime::{verify_miller_bach, CompositeWitness, U256};

let n = U256::from_decimal("1195068768795265792518361315725116351898245581").unwrap();
assert_eq!(verify_miller_bach(&n), Err(CompositeWitness::StrongWitness(37)));
```

## How far you can trust the answers

| Function | Guarantee |
| :--- | :--- |
| `is_prime_u64`, and `is_prime` for `n < 2^64` | Always correct. No unproven assumption. |
| `is_prime` and `verify_miller_bach` for `n >= 2^64` | A prime is always accepted. A composite is always rejected **if the Generalized Riemann Hypothesis (GRH) is true**. |
| `hash_to_prime_256` | Uses `is_prime`, so the output is prime if GRH is true. |
| `sqrt_mod_prime`, `least_nonresidue`, `prime_in_progression_u64` | Every answer is checked before it is returned, so for a prime modulus an answer is never wrong. GRH is only needed to promise that the search finds one within its limit; if GRH were false, these could return an error where an answer exists. |

For large numbers the crate runs Miller-Rabin with every prime base up to about `2 * (ln n)^2`. Eric Bach proved in 1990 that this is enough, but only assuming GRH, which is a famous open problem. A Lean proof of GRH was claimed on 20 November 2026 and is still under review (see [`PROOF.md`](https://github.com/san-digital/det-prime/blob/main/PROOF.md)). Until it is accepted, treat any result above `2^64` as conditional on GRH. If you need a proof of primality that rests on no hypothesis, use a primality certificate (for example ECPP) instead.

## When to use it

- You need the same answer on every machine with no randomness: Wasm guests, consensus code, zkVMs.
- You are checking public numbers that someone may have chosen to fool you, such as a modulus in a protocol message. A fixed table of Miller-Rabin bases can be beaten by a constructed pseudoprime; here the number of bases grows with the input.
- You want `no_std`, zero dependencies, and no `unsafe`.

## When not to use it

- **On secret values.** The code is not constant-time: its running time and branches depend on the input. Do not use it to generate RSA keys or to test any number that must stay secret.
- When you need an unconditional proof that a number above `2^64` is prime (see above).
- When speed matters more than determinism. A 256-bit prime takes tens of milliseconds because about 6,300 bases are tried; a few random Miller-Rabin rounds are much faster.
- For numbers above 4096 bits, which are not supported.

## What is in the crate

| Item | What it does |
| :--- | :--- |
| `is_prime_u64(n)` | Primality of a `u64`. |
| `is_prime(&n)` | Primality of a `U128` ... `U4096` (any `Uint<LIMBS>`). |
| `verify_miller_bach(&n)` | Like `is_prime`, but returns the base or factor that proves `n` composite. |
| `sqrt_mod_prime(&a, &p)` | Square root of `a` modulo a prime `p` (the smaller of the two roots). |
| `least_nonresidue(&p)` | Smallest quadratic non-residue modulo a prime `p`. |
| `hash_to_prime_256(&digest)` | 32-byte hash to a 255-bit prime, e.g. for VDF or Fiat-Shamir challenges. |
| `prime_in_progression_u64(q, a)` | Smallest prime `p` with `p % q == a`, e.g. NTT-friendly primes `p == 1 (mod 2^k)`. |
| `is_prime_be_32`, `sqrt_mod_prime_be_32`, ... | The same functions on big-endian byte buffers. |

Integers parse with `Uint::from_hex`, `Uint::from_decimal`, and `Uint::from_be_bytes`. Full API docs are on [docs.rs](https://docs.rs/det-prime).

## Performance

Single core, `cargo run --release --example timing`, Apple Silicon (M-series), `rustc 1.94.0`:

| Operation | Input | Time |
| :--- | :--- | :--- |
| `is_prime_u64` | 64-bit odd integers (10,000 calls) | 0.97 us per call |
| `is_prime` (`U256`) | 256-bit odd composite | < 0.01 us per call |
| `is_prime` (`U256`) | secp256k1 field prime (all 6,316 prime bases up to 62,973) | 36.3 ms |
| `hash_to_prime_256` | 32-byte digest to 255-bit prime (108 candidates) | 30.2 ms |
| `sqrt_mod_prime` (`U256`) | Stark252 prime (`2^192` divides `p - 1`) | 0.72 ms per call |
| `prime_in_progression_u64` | `q = 2^20, a = 1`, giving `p = 7,340,033` | 1.88 us |

Composites are usually rejected by the first base, so they are fast. Primes are slow because every base must be tried.

## Proofs

The parts that do not need GRH are proved in Lean 4 in [`lean/DetPrime/`](https://github.com/san-digital/det-prime/tree/main/lean/DetPrime): the integer bounds on `ln n` used to pick the number of bases, the fact that testing prime bases is enough, the step from strong liars to Euler-Jacobi liars, and the Tonelli-Shanks invariants. CI compiles and replays these proofs on every pull request. The published analytic bounds (Bach; Lamzouri, Li and Soundararajan) and GRH itself are stated as assumptions, not proved. [`PROOF.md`](https://github.com/san-digital/det-prime/blob/main/PROOF.md) lists exactly what is proved and what is assumed.

## Contributing and security

See [`CONTRIBUTING.md`](https://github.com/san-digital/det-prime/blob/main/CONTRIBUTING.md) for how to build, test, and replay the Lean proofs. Please report security issues privately as described in [`SECURITY.md`](https://github.com/san-digital/det-prime/blob/main/SECURITY.md).

## License

Apache-2.0. See [`LICENSE`](https://github.com/san-digital/det-prime/blob/main/LICENSE).
