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

/// Deterministic verification record returned when Miller-Bach accepts `n`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrimalityCertificate {
    /// Certified integer bound `B >= floor(2 * (ln n)^2)` up to which prime bases apply.
    pub prime_base_bound: u64,
    /// Number of prime bases tested via strong pseudoprime rounds.
    pub bases_tested: u32,
}

/// Unconditional deterministic 64-bit primality test using the 7-base Jim Sinclair
/// witness set `[2, 325, 9375, 28178, 450775, 9780504, 1795265022]`, proven exact
/// across all `0 <= n < 2^64`.
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

/// Runs the full deterministic prime-base Miller-Bach test up to `B = bach_witness_bound(n)`.
///
/// Under `DirichletLNonvanishingRightOfHalf` (and Bach 1990, Theorem 2 + Euler-Jacobi
/// prime-witness reduction in `lean/PrimeWitness.lean`), this test has zero false positives
/// on all inputs up to 4096 bits without using randomness.
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

/// Deterministic, zero-entropy primality test.
///
/// Uses the unconditional 7-base witness set when `n < 2^64`, and the prime-base
/// Miller-Bach test up to `2 * (ln n)^2` when `2^64 <= n < 2^4096`.
pub fn is_prime<const LIMBS: usize>(n: &Uint<LIMBS>) -> bool {
    if let Some(v) = n.as_u64() {
        return is_prime_u64(v);
    }
    verify_miller_bach(n).is_ok()
}
