# Soundness Architecture and Assumption Ledger

`det-prime` separates unconditional machine-checked algebra and integer enclosures from upstream analytic number theory inputs. Every assumption in the chain from Dirichlet L-functions to Rust execution is listed below.

## Three-Tier Assumption Ledger

| Tier | Component | Status | Exact Scope |
| :--- | :--- | :--- | :--- |
| **1. Local Lean 4 proofs (`lean/DetPrime/`)** | Integer logarithm enclosures, subgroup witness reduction, Solovay-Strassen properness, Monier-Rabin strong-liar inclusion, Tonelli-Shanks invariants | **Kernel-replayed (`leanchecker`)**, zero `sorryAx`, axioms `{propext, Classical.choice, Quot.sound}` | Connects real-valued analytic bounds `2 * (ln n)^2` and `(ln p)^2` to exact Rust `u64` / `u128` integer bounds and prime-only witness bases |
| **2. Published explicit analytic theorems** | Bach (1990, Thm 2); Lamzouri, Li & Soundararajan (2015, Cor 1.1 & 1.2); Carneiro, Milinovich & Soundararajan (2019, Thm 5) | **Peer-reviewed mathematics**; stated explicitly as typed `Prop` hypotheses in `lean/DetPrime/BridgeAudit.lean` | Converts zero-free half-plane hypotheses (`DirichletLNonvanishingRightOfHalf`, `RiemannZetaZerosOnLine`) into explicit numerical constants `2 * (ln n)^2`, `(ln p)^2`, `(phi(q) * ln q)^2`, and `(22/25) * sqrt(x) * ln(x)` |
| **3. Upstream zero-free half-plane proofs** | `DirichletLNonvanishingRightOfHalf` and `RiemannZetaZerosOnLine` (`Statements.lean`, Levent Alpoge, 20 Nov 2026) | **Externally kernel-checked in Lean 4** (including independent checkers `nanoda` and `con-leche`, documented by Andrew Sutherland at MIT); human mathematical peer review ongoing | Discharges the GRH / RH antecedents in Tier 2 when accepted; for `n < 2^64`, `is_prime_u64` uses Sinclair's 7-base witness set and depends on neither Tier 2 nor Tier 3 |

## Module-by-Module Mapping (`lean/DetPrime/` -> `src/`)

### 1. `DetPrime.LogBounds` -> `src/bounds.rs`

Rust computes witness bounds without `f64` hardware instructions so results stay identical across x86_64, ARM64, RISC-V, and `wasm32-unknown-unknown`. Given `n >= 2`, `Uint::log2_mantissa4` extracts `(k, m)` with `0 <= m <= 15` and `n < 2^k * (17 + m) / 16`.

`LogBounds.lean` mirrors `ln_upper_scaled`, `bach_bound_from_km`, and `lls_bound_from_km` with identical integer constants (`LN2_SCALED_HI = 6_931_471_808`, `LOG_SCALE = 10_000_000_000`):

- `lnUpperScaled_strict_bound`: Proves `Real.log n < lnUpperScaled k m / 10^10` from Mathlib's `Real.log_two_lt_d9` and `Real.log_le_sub_one_of_pos` applied to `(17 + m) / 16` and `(17 + m) / 32`.
- `bachBound_sound`: Proves that every natural number `a` with `(a : Real) <= 2 * (Real.log n)^2` satisfies `a <= bachBoundFromKm k m`.
- `llsBound_sound`: Proves that every natural number `a` with `(a : Real) <= (Real.log n)^2` satisfies `a <= llsBoundFromKm k m`.
- `bachBound_u256_max`: Kernel `rfl` check confirming `bachBoundFromKm 255 15 = 62973`, matching `bach_witness_bound(&(2^256 - 1))` in `tests/bounds_and_sieve.rs`.

### 2. `DetPrime.PrimeWitness` -> `src/primality.rs`

`verify_miller_bach` tests only **prime** bases `p <= bach_witness_bound(n)` via strong probable prime rounds in Montgomery form. `PrimeWitness.lean` proves every finite-group and number-theoretic step required for prime-only bases:

- `prime_witness_of_coprime_witness`: For any subgroup `H <= (ZMod n)^x`, if a coprime integer `1 <= a <= B` lies outside `H`, some prime factor `p <= B` of `a` also lies outside `H`.
- `eulerJacobiSubgroup`: Proves `{u in (ZMod n)^x | u^((n - 1)/2) = J(u | n)}` is a subgroup of `(ZMod n)^x` for every integer `n > 1`.
- `odd_composite_exists_euler_jacobi_witness` (Solovay-Strassen): Proves from scratch (via Chinese Remainder Theorem on squarefree composites and nilpotent lifts `1 + n/p` on non-squarefree composites) that `eulerJacobiSubgroup n` is a proper subgroup of `(ZMod n)^x` for every odd composite `n > 1`.
- `strong_liar_mem_euler_jacobi` (Monier-Rabin / Pomerance-Selfridge-Wagstaff): Proves from scratch that every strong probable prime base coprime to an odd integer `n > 1` lies inside `eulerJacobiSubgroup n`.
- `prime_is_strong_probable_prime`: Proves every prime passes `IsStrongProbablePrime` for all coprime bases (zero false negatives).

### 3. `DetPrime.TonelliShanks` -> `src/field.rs`

- `squaresSubgroup` and `prime_nonresidue_witness`: Proves that if a prime `p` has any quadratic non-residue `1 <= a <= B`, it has a **prime** quadratic non-residue `q <= B`, justifying prime-only iteration in `least_nonresidue`.
- `sqrt_three_mod_four`: Proves `(a^((p + 1)/4))^2 = a` for all quadratic residues when `p % 4 = 3`.
- `tonelli_shanks_init`, `tonelli_shanks_step`, and `tonelli_shanks_done`: Proves initialization, preservation of `r^2 = a * t` and `c^(2^(m-1)) = -1`, strict decrease of the 2-adic exponent `i < m` (`t'^(2^(i-1)) = 1`), and termination `t = 1 -> r^2 = a`.

### 4. `DetPrime.BridgeAudit` -> End-to-End Composition

- `miller_bach_prime_iff_all_prime_bases`: Combines `BachSubgroupBound`, `bachBound_sound`, `odd_composite_exists_euler_jacobi_witness`, `prime_witness_of_coprime_witness`, `strong_liar_mem_euler_jacobi`, and `prime_is_strong_probable_prime` into a single equivalence: an odd integer `n > 1` is prime if and only if every prime `p <= bachBoundFromKm k m` coprime to `n` passes `IsStrongProbablePrime`.
- `least_nonresidue_has_prime_witness`: Combines `LLSNonresidueBound`, `llsBound_sound`, and `prime_nonresidue_witness` to guarantee a prime quadratic non-residue `q <= llsBoundFromKm k m` for every prime `p >= 5`.

## Replaying the Proofs Locally

With Lean `v4.33.1` (or compatible Mathlib4 checkout) installed:

```sh
MATHLIB_DIR=/path/to/mathlib4 ./lean/replay.sh
```

To include the `rfl` definitional-equality check against Alpoge's `Statements.lean`:

```sh
MATHLIB_DIR=/path/to/mathlib4 ALPOGE_STATEMENTS=/path/to/Statements.lean ./lean/replay.sh
```

## Primary References

1. Eric Bach, "Explicit bounds for primality testing and related problems," *Mathematics of Computation* 55(191), 355-380 (1990).
2. Youness Lamzouri, Xiannan Li, and Kannan Soundararajan, "Conditional bounds for the least quadratic non-residue and related problems," *Mathematics of Computation* 84(295), 2391-2412 (2015).
3. Emanuel Carneiro, Micah B. Milinovich, and Kannan Soundararajan, "Fourier optimization and prime gaps," *Forum Mathematicum* 31(4), 859-880 (2019).
4. Francois Arnault, "Constructing Carmichael numbers which are strong pseudoprimes to several bases," *Journal of Symbolic Computation* 20(2), 151-161 (1995).
5. Jonathan Sorenson and Jonathan Webster, "Strong pseudoprimes to twelve prime bases," *Mathematics of Computation* 86(304), 985-1003 (2017).
6. Levent Alpoge, *On the Riemann Hypothesis* (`remark.pdf` and `Statements.lean`, 20 November 2026); independent Lean 4 kernel replay logs maintained by Andrew Sutherland (`mit.edu/~drew`).
