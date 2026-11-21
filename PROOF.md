# Proofs and assumptions

This file lists what `det-prime` proves in Lean, what it takes from published papers, and what it simply assumes.

## Summary

- `is_prime_u64`, and `is_prime` for `n < 2^64`, depend on none of the material below. They use Jim Sinclair's 7 Miller-Rabin bases, which are known from exhaustive computation to be correct for every `n < 2^64`. No hypothesis is involved.
- For `n >= 2^64`, `is_prime` and `verify_miller_bach` accept every prime unconditionally (proved in Lean). That they reject every composite rests on Bach's 1990 theorem, which assumes the Generalized Riemann Hypothesis (GRH).
- `least_nonresidue`, `sqrt_mod_prime`, and `prime_in_progression_u64` check each answer before returning it. GRH is used only to guarantee that a search finds an answer within its limit.

## The three layers

| Layer | What it covers | Status |
| :--- | :--- | :--- |
| 1. Lean proofs in `lean/DetPrime/` | Integer bounds on `ln n`; reduction to prime bases; Solovay-Strassen properness of the Euler-Jacobi subgroup; strong liars are Euler-Jacobi liars; primes pass every base; Tonelli-Shanks invariants | Machine-checked. CI compiles the modules, replays them with `leanchecker`, and fails if any theorem uses an axiom other than `propext`, `Classical.choice`, and `Quot.sound` (so no `sorry` and no `native_decide`). |
| 2. Published analytic bounds | Bach (1990, Thm 2); Lamzouri, Li & Soundararajan (2015, Cor 1.1 & 1.2); Carneiro, Milinovich & Soundararajan (2019, Thm 5) | Peer-reviewed results, each assuming GRH or RH. They are not formalized: `lean/DetPrime/BridgeAudit.lean` states them as hypotheses (`BachSubgroupBound`, `LLSNonresidueBound`, `LLSProgressionBound`, `CMSPrimeGapBound`). The last two are stated but not yet used by any theorem. |
| 3. GRH and RH | `DirichletLNonvanishingRightOfHalf` (GRH) and `RiemannZetaZerosOnLine` (RH) | Long-standing open conjectures, taken as hypotheses. See the next section. |

The end-to-end theorems in `BridgeAudit.lean` therefore take GRH and the relevant published bound as explicit arguments. They show that the Rust algorithm is correct if those inputs are true; they do not prove the inputs.

## The claimed proof of GRH

On 20 November 2026 Levent Alpöge released a Lean 4 development, with an accompanying essay (`remark.pdf`), that claims to prove RH and GRH. Press reports say that other people, including Andrew Sutherland (MIT), have compiled it successfully. Whether its formal statements match the classical conjectures, and whether the mathematical community accepts the proof, are still under review.

`det-prime` does not depend on that work. It states the two hypotheses itself, in `BridgeAudit.lean`. The definitions are intended to be identical to those in Alpöge's `Statements.lean`, and `lean/replay.sh` checks this with `rfl` when you pass that file (see below). If the proof is accepted, layer 3 is discharged. Until then, treat results above `2^64` as conditional on GRH.

## How the Lean modules map to the Rust code

### `DetPrime.LogBounds` and `src/bounds.rs`

Rust computes the base limits with integer arithmetic only (no `f64`), so results are identical on x86_64, ARM64, RISC-V, and `wasm32-unknown-unknown`. Given `n >= 2`, `Uint::log2_mantissa4` returns `(k, m)` with `0 <= m <= 15` and `n < 2^k * (17 + m) / 16`.

`LogBounds.lean` defines `lnUpperScaled`, `bachBoundFromKm`, and `llsBoundFromKm` with the same integer constants as the Rust code (`LN2_SCALED_HI = 6_931_471_808`, `LOG_SCALE = 10_000_000_000`):

- `lnUpperScaled_strict_bound`: `Real.log n < lnUpperScaled k m / 10^10`, from Mathlib's `Real.log_two_lt_d9` and `Real.log_le_sub_one_of_pos` applied to `(17 + m) / 16` and `(17 + m) / 32`.
- `bachBound_sound`: every natural number `a` with `(a : Real) <= 2 * (Real.log n)^2` satisfies `a <= bachBoundFromKm k m`.
- `llsBound_sound`: every natural number `a` with `(a : Real) <= (Real.log n)^2` satisfies `a <= llsBoundFromKm k m`.
- `bachBound_u256_max`: `bachBoundFromKm 255 15 = 62973` by `rfl`, matching `bach_witness_bound(&(2^256 - 1))` in `tests/bounds_and_sieve.rs`.

### `DetPrime.PrimeWitness` and `src/primality.rs`

`verify_miller_bach` tests only prime bases `p <= bach_witness_bound(n)`. `PrimeWitness.lean` proves the group theory and number theory that make prime bases enough:

- `prime_witness_of_coprime_witness`: for any subgroup `H <= (ZMod n)^x`, if a coprime integer `1 <= a <= B` lies outside `H`, some prime factor `p <= B` of `a` also lies outside `H`.
- `eulerJacobiSubgroup`: `{u in (ZMod n)^x | u^((n - 1)/2) = J(u | n)}` is a subgroup of `(ZMod n)^x` for every `n > 1`.
- `odd_composite_exists_euler_jacobi_witness` (Solovay-Strassen): for every odd composite `n > 1`, `eulerJacobiSubgroup n` is a proper subgroup. The proof uses the Chinese Remainder Theorem for squarefree `n` and the element `1 + n/p` otherwise.
- `strong_liar_mem_euler_jacobi` (Monier-Rabin, Pomerance-Selfridge-Wagstaff): every base coprime to an odd `n > 1` that passes the strong probable prime test lies in `eulerJacobiSubgroup n`.
- `prime_is_strong_probable_prime`: every prime passes the strong probable prime test for every coprime base, so a prime is never rejected.

### `DetPrime.TonelliShanks` and `src/field.rs`

- `squaresSubgroup` and `prime_nonresidue_witness`: if a prime `p` has a quadratic non-residue `1 <= a <= B`, it has a prime one `q <= B`, so `least_nonresidue` only needs to try primes.
- `sqrt_three_mod_four`: `(a^((p + 1)/4))^2 = a` for every square `a` when `p % 4 = 3`.
- `tonelli_shanks_init`, `tonelli_shanks_step`, and `tonelli_shanks_done`: the loop starts correctly, each step keeps `r^2 = a * t` and `c^(2^(m-1)) = -1` while the 2-adic order of `t` strictly drops, and `t = 1` implies `r^2 = a`.

### `DetPrime.BridgeAudit`: putting it together

- `miller_bach_prime_iff_all_prime_bases`: assuming GRH and `BachSubgroupBound`, and using `bachBound_sound`, `odd_composite_exists_euler_jacobi_witness`, `prime_witness_of_coprime_witness`, `strong_liar_mem_euler_jacobi`, and `prime_is_strong_probable_prime`: an odd `n > 1` is prime if and only if every prime `p <= bachBoundFromKm k m` coprime to `n` passes the strong probable prime test.
- `least_nonresidue_has_prime_witness`: assuming GRH and `LLSNonresidueBound`, and using `llsBound_sound` and `prime_nonresidue_witness`: every prime `p >= 5` has a prime quadratic non-residue `q <= llsBoundFromKm k m`.

## Replaying the proofs locally

With a Mathlib4 checkout at tag `v4.33.1` (the version CI uses) and its cache downloaded:

```sh
MATHLIB_DIR=/path/to/mathlib4 ./lean/replay.sh
```

The `lean` CI job runs the same script on every push and pull request.

To also check that the GRH and RH definitions are identical (`rfl`) to those in Alpöge's `Statements.lean`:

```sh
MATHLIB_DIR=/path/to/mathlib4 ALPOGE_STATEMENTS=/path/to/Statements.lean ./lean/replay.sh
```

## References

1. Eric Bach, "Explicit bounds for primality testing and related problems," *Mathematics of Computation* 55(191), 355-380 (1990).
2. Youness Lamzouri, Xiannan Li, and Kannan Soundararajan, "Conditional bounds for the least quadratic non-residue and related problems," *Mathematics of Computation* 84(295), 2391-2412 (2015).
3. Emanuel Carneiro, Micah B. Milinovich, and Kannan Soundararajan, "Fourier optimization and prime gaps," *Commentarii Mathematici Helvetici* 94(3), 533-568 (2019), doi:10.4171/CMH/467.
4. Francois Arnault, "Constructing Carmichael numbers which are strong pseudoprimes to several bases," *Journal of Symbolic Computation* 20(2), 151-161 (1995).
5. Jonathan Sorenson and Jonathan Webster, "Strong pseudoprimes to twelve prime bases," *Mathematics of Computation* 86(304), 985-1003 (2017).
6. Levent Alpöge, claimed Lean 4 proof of RH and GRH, with the essay `remark.pdf` and the file `Statements.lean` (released 20 November 2026; under review, not yet accepted).
