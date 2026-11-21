use crate::bounds::{bach_witness_bound, lls_nonresidue_bound, progression_prime_bound};
use crate::primality::{is_prime, is_prime_u64};
use crate::sieve::PrimeIter;
use crate::uint::{MontCtx, Uint, U256};
use crate::Error;

/// Computes the Jacobi symbol `J(a | n)` in `{-1, 0, 1}` for `n` odd (`n >= 3`).
#[inline]
pub fn jacobi_u64(mut a: u64, mut n: u64) -> i8 {
    debug_assert!(n >= 3 && (n & 1) == 1);
    a %= n;
    let mut res = 1i8;
    while a != 0 {
        let tz = a.trailing_zeros();
        if (tz & 1) == 1 {
            let n8 = n & 7;
            if n8 == 3 || n8 == 5 {
                res = -res;
            }
        }
        a >>= tz;
        if (a & 3) == 3 && (n & 3) == 3 {
            res = -res;
        }
        core::mem::swap(&mut a, &mut n);
        a %= n;
    }
    if n == 1 {
        res
    } else {
        0
    }
}

/// Computes `J(q | p)` for a prime `q >= 2` and an odd `Uint<LIMBS>` `p >= 3`.
#[inline]
pub fn jacobi_prime_mod_odd<const LIMBS: usize>(q: u64, p: &Uint<LIMBS>) -> i8 {
    debug_assert!(p.is_odd());
    if q == 2 {
        let p8 = p.0[0] & 7;
        return if p8 == 1 || p8 == 7 { 1 } else { -1 };
    }
    let rem = p.rem_u64(q);
    if rem == 0 {
        return 0;
    }
    let flip = (q & 3) == 3 && (p.0[0] & 3) == 3;
    let j = jacobi_u64(rem, q);
    if flip {
        -j
    } else {
        j
    }
}

/// Finds the smallest prime quadratic non-residue `z` modulo an odd prime `p >= 3`.
///
/// Under `DirichletLNonvanishingRightOfHalf` (Lamzouri, Li, and Soundararajan 2015,
/// Corollary 1.1; Bach 1990, Theorem 2), a prime non-residue exists below `(ln p)^2`
/// for all primes `p >= 5` (and `z = 2` for `p = 3`). Verifies Euler's criterion
/// `z^((p - 1)/2) == -1 (mod p)` before returning.
pub fn least_nonresidue<const LIMBS: usize>(p: &Uint<LIMBS>) -> Result<u64, Error> {
    if p.is_even() || *p <= Uint::TWO {
        return Err(Error::InvalidModulus);
    }
    let ctx = MontCtx::new(*p).ok_or(Error::InvalidModulus)?;
    let half = p.wrapping_sub(&Uint::ONE).shr(1);

    // Search up to LLS bound first, falling back to Bach's 2*(ln p)^2 bound.
    let bound = bach_witness_bound(p).max(lls_nonresidue_bound(p));
    let small_p = p.as_u64();

    for q in PrimeIter::up_to(bound) {
        if let Some(pv) = small_p {
            if q >= pv {
                return Err(Error::CompositeModulus);
            }
        }
        let j = jacobi_prime_mod_odd(q, p);
        if j == 0 {
            return Err(Error::CompositeModulus);
        }
        if j == -1 {
            let q_mont = ctx.u64_to_mont(q);
            let euler = ctx.pow(&q_mont, &half);
            if euler != ctx.neg_one() {
                return Err(Error::CompositeModulus);
            }
            return Ok(q);
        }
    }
    Err(Error::CompositeModulus)
}

/// Deterministic, zero-entropy modular square root modulo an odd prime `p >= 3`.
///
/// Given `0 <= a < p`, returns:
/// - `Ok(Some(r))` with `0 <= r <= (p - 1)/2` and `r^2 == a (mod p)` if `a` is a square mod `p`,
/// - `Ok(None)` if `a` is a quadratic non-residue mod `p`,
/// - `Err(_)` if `p` is invalid/composite or `a >= p`.
pub fn sqrt_mod_prime<const LIMBS: usize>(
    a: &Uint<LIMBS>,
    p: &Uint<LIMBS>,
) -> Result<Option<Uint<LIMBS>>, Error> {
    if p.is_even() || *p <= Uint::TWO {
        return Err(Error::InvalidModulus);
    }
    if a >= p {
        return Err(Error::OutOfRange);
    }
    if a.is_zero() {
        return Ok(Some(Uint::ZERO));
    }

    let ctx = MontCtx::new(*p).ok_or(Error::InvalidModulus)?;
    let a_mont = ctx.to_mont(a);
    let p_minus_one = p.wrapping_sub(&Uint::ONE);
    let half = p_minus_one.shr(1);

    let euler = ctx.pow(&a_mont, &half);
    if euler == ctx.neg_one() {
        return Ok(None);
    }
    if euler != ctx.one() {
        return Err(Error::CompositeModulus);
    }

    let root_mont = if (p.0[0] & 3) == 3 {
        // p == 3 (mod 4): r = a^((p + 1) / 4) mod p, where (p + 1) / 4 = ((p - 3) >> 2) + 1.
        let exp = p
            .wrapping_sub(&Uint::from_u64(3))
            .shr(2)
            .checked_add_u64(1)
            .ok_or(Error::Overflow)?;
        ctx.pow(&a_mont, &exp)
    } else {
        // General Tonelli-Shanks with deterministic prime quadratic non-residue z.
        let z = least_nonresidue(p)?;
        let s = p_minus_one.trailing_zeros();
        let q = p_minus_one.shr(s);
        let q_plus_one_half = q.shr(1).checked_add_u64(1).ok_or(Error::Overflow)?;

        let z_mont = ctx.u64_to_mont(z);
        let mut c = ctx.pow(&z_mont, &q);
        let mut t = ctx.pow(&a_mont, &q);
        let mut r = ctx.pow(&a_mont, &q_plus_one_half);
        let mut m = s;

        while t != ctx.one() {
            let mut t_pow = t;
            let mut i = 0u32;
            while i < m && t_pow != ctx.one() {
                t_pow = ctx.sqr(&t_pow);
                i += 1;
            }
            if i == 0 || i >= m {
                return Err(Error::CompositeModulus);
            }

            let mut b = c;
            for _ in 0..(m - i - 1) {
                b = ctx.sqr(&b);
            }
            m = i;
            c = ctx.sqr(&b);
            t = ctx.mul(&t, &c);
            r = ctx.mul(&r, &b);
        }
        r
    };

    // Verify r^2 == a (mod p) before returning, guarding against Carmichael moduli.
    if ctx.sqr(&root_mont) != a_mont {
        return Err(Error::CompositeModulus);
    }

    let root = ctx.from_mont(&root_mont);
    let neg_root = p.wrapping_sub(&root);
    let canonical = if neg_root < root { neg_root } else { root };
    Ok(Some(canonical))
}

/// Finds the smallest prime `>= start` within `max_odd_steps` odd candidates,
/// returning `(prime, odd_candidates_tested)`.
pub fn next_prime_bounded<const LIMBS: usize>(
    start: &Uint<LIMBS>,
    max_odd_steps: u32,
) -> Result<(Uint<LIMBS>, u32), Error> {
    if max_odd_steps == 0 {
        return Err(Error::StepBudgetExceeded);
    }
    if *start <= Uint::TWO {
        return Ok((Uint::TWO, 1));
    }
    let mut cand = *start;
    if cand.is_even() {
        cand = cand.checked_add_u64(1).ok_or(Error::Overflow)?;
    }
    for step in 1..=max_odd_steps {
        if is_prime(&cand) {
            return Ok((cand, step));
        }
        if step < max_odd_steps {
            cand = cand.checked_add_u64(2).ok_or(Error::Overflow)?;
        }
    }
    Err(Error::StepBudgetExceeded)
}

/// Default deterministic step cap for 256-bit `hash_to_prime_256` (`16,384` odd steps).
/// At 255 bits (`ln n ~ 176.7`), average steps to hit a prime is ~88, and `(ln n)^2 ~ 31,240`
/// spans ~15,620 odd candidates.
pub const DEFAULT_HASH_TO_PRIME_STEPS: u32 = 16_384;

/// Maps a 32-byte digest deterministically to a 255-bit prime in `[2^254 + 1, 2^255)`
/// for verifiable delay functions (Wesolowski VDFs), RSA accumulators, and Fiat-Shamir
/// transcript challenges without randomness.
///
/// Clears bit 255 (avoiding overflow near `2^256 - 1`), sets bit 254 (enforcing 255-bit
/// security floor), sets bit 0 (odd), and steps by `+2` using deterministic Miller-Bach.
pub fn hash_to_prime_256(digest: &[u8; 32]) -> Result<(U256, u32), Error> {
    hash_to_prime_256_bounded(digest, DEFAULT_HASH_TO_PRIME_STEPS)
}

/// Configurable step-cap variant of `hash_to_prime_256`.
pub fn hash_to_prime_256_bounded(
    digest: &[u8; 32],
    max_odd_steps: u32,
) -> Result<(U256, u32), Error> {
    let mut buf = *digest;
    buf[0] = (buf[0] & 0x7f) | 0x40;
    buf[31] |= 0x01;
    let start = U256::from_be_bytes(&buf)?;
    next_prime_bounded(&start, max_odd_steps)
}

/// Finds the smallest prime `p == a (mod q)` for `q > 3` and `gcd(a, q) == 1`.
///
/// Under `DirichletLNonvanishingRightOfHalf` (Lamzouri, Li, and Soundararajan 2015,
/// Corollary 1.2), such a prime exists with `p <= (phi(q) * ln q)^2`.
/// Returns `(prime, progression_steps_tested)`.
pub fn prime_in_progression_u64(q: u64, a: u64) -> Result<(u64, u64), Error> {
    if q <= 3 {
        return Err(Error::InvalidModulus);
    }
    let rem = a % q;
    if rem == 0 || gcd_u64(rem, q) != 1 {
        return Err(Error::NotCoprime);
    }
    let phi = euler_totient_u64(q);
    let bound = progression_prime_bound(q, phi).ok_or(Error::Overflow)?;
    let cap = bound.min(u64::MAX as u128) as u64;

    let mut cand = rem;
    let mut steps = 0u64;
    loop {
        steps += 1;
        if cand >= 2 && is_prime_u64(cand) {
            return Ok((cand, steps));
        }
        match cand.checked_add(q) {
            Some(next) if next <= cap => cand = next,
            _ => return Err(Error::StepBudgetExceeded),
        }
    }
}

#[inline]
const fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Computes Euler's totient `phi(n)` for `n >= 1` by deterministic trial factorization.
pub fn euler_totient_u64(mut n: u64) -> u64 {
    if n <= 1 {
        return n;
    }
    let mut result = n;
    if (n & 1) == 0 {
        result -= result / 2;
        while (n & 1) == 0 {
            n >>= 1;
        }
    }
    let mut d = 3u64;
    while (d as u128) * (d as u128) <= (n as u128) {
        if n % d == 0 {
            result -= result / d;
            while n % d == 0 {
                n /= d;
            }
        }
        d += 2;
    }
    if n > 1 {
        result -= result / n;
    }
    result
}
