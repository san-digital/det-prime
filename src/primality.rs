//! Primality tests: [`is_prime_u64`], [`is_prime`], and [`verify_miller_bach`].

use crate::bounds::{bach_witness_bound, MAX_SIEVE_BITS};
use crate::sieve::{PrimeIter, MAX_SIEVE_LIMIT, SMALL_ODD_PRIMES};
use crate::uint::{MontCtx, Uint};

/// Explicit reason why a candidate integer was rejected as composite (or `< 2`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompositeWitness {
    /// Input is `0` or `1`.
    LessThanTwo,
    /// Input is an even integer greater than `2`.
    Even,
    /// Input is divisible by the given prime factor `< n`.
    PrimeFactor(u64),
    /// Input failed the strong pseudoprime test at the given prime base.
    StrongWitness(u64),
    /// Input bit width exceeds the supported 4096-bit sieve range.
    ModulusTooLarge,
}

/// Summary of a successful [`verify_miller_bach`] run.
///
/// This records which bases were tried. It is not a primality certificate that a third
/// party can check without re-running the test, and it inherits the GRH assumption
/// described on [`verify_miller_bach`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrimalityCertificate {
    /// Certified integer bound `B >= floor(2 * (ln n)^2)` up to which prime bases apply.
    pub prime_base_bound: u64,
    /// Number of prime bases tested via strong pseudoprime rounds.
    pub bases_tested: u32,
}

/// Primality test for `u64`. Always correct: no unproven hypothesis is involved.
///
/// Runs Miller-Rabin with Jim Sinclair's 7 bases
/// `[2, 325, 9375, 28178, 450775, 9780504, 1795265022]`, which are known (by exhaustive
/// computation) to give the right answer for every `n < 2^64`.
pub fn is_prime_u64(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    if n == 2 || n == 3 || n == 5 || n == 7 {
        return true;
    }
    if (n & 1) == 0 || n % 3 == 0 || n % 5 == 0 || n % 7 == 0 {
        return false;
    }
    if n < 121 {
        return true;
    }

    const BASES: [u64; 7] = [2, 325, 9375, 28178, 450775, 9780504, 1795265022];
    let s = (n - 1).trailing_zeros();
    let d = (n - 1) >> s;

    for base in BASES {
        let a = base % n;
        if a == 0 {
            continue;
        }
        if !strong_probable_prime_u64(a, n, d, s) {
            return false;
        }
    }
    true
}

#[inline]
fn mod_pow_u64(mut base: u64, mut exp: u64, m: u64) -> u64 {
    let mut result = 1u64;
    let m128 = m as u128;
    base %= m;
    while exp > 0 {
        if (exp & 1) != 0 {
            result = (((result as u128) * (base as u128)) % m128) as u64;
        }
        base = (((base as u128) * (base as u128)) % m128) as u64;
        exp >>= 1;
    }
    result
}

#[inline]
fn strong_probable_prime_u64(a: u64, n: u64, d: u64, s: u32) -> bool {
    let mut x = mod_pow_u64(a, d, n);
    if x == 1 || x == n - 1 {
        return true;
    }
    let m128 = n as u128;
    for _ in 1..s {
        x = (((x as u128) * (x as u128)) % m128) as u64;
        if x == n - 1 {
            return true;
        }
        if x == 1 {
            return false;
        }
    }
    false
}

/// Runs Miller-Rabin with every prime base up to `B = bach_witness_bound(n)` (about
/// `2 * (ln n)^2`) and reports either a summary or the reason `n` is composite.
///
/// A prime `n` is always accepted; that part needs no assumption. Rejecting every composite
/// relies on Bach's theorem (1990, Theorem 2), which assumes the Generalized Riemann
/// Hypothesis (GRH). If GRH holds, this test never accepts a composite up to 4096 bits.
/// GRH is unproven, so treat a pass for `n >= 2^64` as "prime, assuming GRH". See
/// `PROOF.md` and `lean/DetPrime/PrimeWitness.lean` for the details.
pub fn verify_miller_bach<const LIMBS: usize>(
    n: &Uint<LIMBS>,
) -> Result<PrimalityCertificate, CompositeWitness> {
    if n.is_zero() || n.is_one() {
        return Err(CompositeWitness::LessThanTwo);
    }
    if *n == Uint::TWO {
        return Ok(PrimalityCertificate {
            prime_base_bound: 2,
            bases_tested: 0,
        });
    }
    if n.is_even() {
        return Err(CompositeWitness::Even);
    }
    if n.bits() > MAX_SIEVE_BITS {
        return Err(CompositeWitness::ModulusTooLarge);
    }

    // Fast pre-screen against the first 64 odd primes before constructing Montgomery context.
    let small_n = n.as_u64();
    for &p16 in &SMALL_ODD_PRIMES[..64] {
        let p = p16 as u64;
        if let Some(v) = small_n {
            if v == p {
                return Ok(PrimalityCertificate {
                    prime_base_bound: bach_witness_bound(n),
                    bases_tested: 0,
                });
            }
            if (p as u128) * (p as u128) > (v as u128) {
                return Ok(PrimalityCertificate {
                    prime_base_bound: bach_witness_bound(n),
                    bases_tested: 0,
                });
            }
        }
        if n.rem_u64(p) == 0 {
            return Err(CompositeWitness::PrimeFactor(p));
        }
    }

    let bound = bach_witness_bound(n);
    if bound > MAX_SIEVE_LIMIT {
        return Err(CompositeWitness::ModulusTooLarge);
    }

    let ctx = MontCtx::new(*n).ok_or(CompositeWitness::LessThanTwo)?;
    let n_minus_one = n.wrapping_sub(&Uint::ONE);
    let s = n_minus_one.trailing_zeros();
    let d = n_minus_one.shr(s);

    // Test base 2 first; catches over 99.9% of remaining random composites in one round.
    if !strong_probable_prime_mont(&ctx, 2, &d, s) {
        return Err(CompositeWitness::StrongWitness(2));
    }
    let mut bases_tested = 1u32;

    for p in PrimeIter::up_to(bound) {
        if p == 2 {
            continue;
        }
        if let Some(v) = small_n {
            if v == p {
                return Ok(PrimalityCertificate {
                    prime_base_bound: bound,
                    bases_tested,
                });
            }
            if (p as u128) * (p as u128) > (v as u128) {
                return Ok(PrimalityCertificate {
                    prime_base_bound: bound,
                    bases_tested,
                });
            }
            if v % p == 0 {
                return Err(CompositeWitness::PrimeFactor(p));
            }
        }

        if !strong_probable_prime_mont(&ctx, p, &d, s) {
            if n.rem_u64(p) == 0 {
                return Err(CompositeWitness::PrimeFactor(p));
            }
            return Err(CompositeWitness::StrongWitness(p));
        }
        bases_tested += 1;
    }

    Ok(PrimalityCertificate {
        prime_base_bound: bound,
        bases_tested,
    })
}

#[inline]
pub(crate) fn strong_probable_prime_mont<const LIMBS: usize>(
    ctx: &MontCtx<LIMBS>,
    base: u64,
    d: &Uint<LIMBS>,
    s: u32,
) -> bool {
    let a_mont = ctx.u64_to_mont(base);
    let mut x = ctx.pow(&a_mont, d);
    let one = ctx.one();
    let neg_one = ctx.neg_one();
    if x == one || x == neg_one {
        return true;
    }
    for _ in 1..s {
        x = ctx.sqr(&x);
        if x == neg_one {
            return true;
        }
        if x == one {
            return false;
        }
    }
    false
}

/// Primality test for fixed-width integers. Uses no randomness.
///
/// - `n < 2^64`: calls [`is_prime_u64`]. Always correct.
/// - `2^64 <= n < 2^4096`: calls [`verify_miller_bach`]. A prime always returns `true`.
///   A composite returns `false` provided the Generalized Riemann Hypothesis (GRH) holds.
///
/// The running time and branches depend on `n`, so do not use this on secret values.
///
/// Returns `false` for `n >= 2^4096` (reachable only with `LIMBS > 64`) without testing it;
/// call [`verify_miller_bach`] to tell that case (`CompositeWitness::ModulusTooLarge`) apart
/// from a composite.
pub fn is_prime<const LIMBS: usize>(n: &Uint<LIMBS>) -> bool {
    if let Some(v) = n.as_u64() {
        return is_prime_u64(v);
    }
    verify_miller_bach(n).is_ok()
}
