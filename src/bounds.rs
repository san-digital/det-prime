//! Integer upper bounds on `ln n` and the search limits derived from it (no floating point).

use crate::uint::Uint;

/// Maximum input bit width supported by the stack-allocated prime sieve (`4096` bits).
pub const MAX_SIEVE_BITS: u32 = 4096;

/// Rational upper bound for `10^10 * ln(2)`, matching Mathlib's `Real.log_two_lt_d9`.
pub const LN2_SCALED_HI: u128 = 6_931_471_808;

/// Exact scale `10^10`.
pub const LOG_SCALE: u128 = 10_000_000_000;

/// Exact squared scale `10^20`.
pub const LOG_SCALE_SQ: u128 = LOG_SCALE * LOG_SCALE;

/// Upper bound on `10^10 * ln(n)` given `(k, m)` with `0 <= m <= 15` and
/// `n < 2^k * (17 + m) / 16`.
///
/// Uses `ln((17 + m)/16) <= min((m + 1)/16, ln(2) - (15 - m)/32)`.
/// Proved strictly above `10^10 * ln(n)` in `lean/DetPrime/LogBounds.lean`.
#[inline]
pub const fn ln_upper_scaled(k: u32, m: u32) -> u128 {
    let m_clamped = if m > 15 { 15 } else { m } as u128;
    let frac_left = 625_000_000u128 * (m_clamped + 1);
    let frac_right = LN2_SCALED_HI - 312_500_000u128 * (15 - m_clamped);
    let frac = if frac_left < frac_right {
        frac_left
    } else {
        frac_right
    };
    LN2_SCALED_HI * (k as u128) + frac
}

/// Certified integer upper bound `B` such that every positive integer `a < 2 * (ln n)^2`
/// satisfies `a <= B`. Matches `DetPrime.bachBoundFromKm` in `lean/DetPrime/LogBounds.lean`.
#[inline]
pub const fn bach_bound_from_km(k: u32, m: u32) -> u64 {
    let ln_hi = ln_upper_scaled(k, m);
    ((2u128 * ln_hi * ln_hi) / LOG_SCALE_SQ) as u64
}

/// Certified integer upper bound `B` such that every positive integer `a < (ln n)^2`
/// satisfies `a <= B`. Matches `DetPrime.llsBoundFromKm` in `lean/DetPrime/LogBounds.lean`.
#[inline]
pub const fn lls_bound_from_km(k: u32, m: u32) -> u64 {
    let ln_hi = ln_upper_scaled(k, m);
    ((ln_hi * ln_hi) / LOG_SCALE_SQ) as u64
}

/// Bach (1990, Theorem 2) witness bound `floor(2 * ln_hi(n)^2)` for `n >= 2`, where `ln_hi(n)`
/// is a slightly rounded-up `ln n`. Bach's theorem that this many bases suffice assumes GRH.
#[inline]
pub const fn bach_witness_bound<const LIMBS: usize>(n: &Uint<LIMBS>) -> u64 {
    let (k, m) = n.log2_mantissa4();
    if k == 0 && m == 0 {
        return 2;
    }
    let b = bach_witness_raw(k, m);
    if b < 2 {
        2
    } else {
        b
    }
}

#[inline]
const fn bach_witness_raw(k: u32, m: u32) -> u64 {
    bach_bound_from_km(k, m)
}

/// Lamzouri, Li, and Soundararajan (2015, Corollary 1.1) least quadratic non-residue
/// bound `floor(ln_hi(p)^2)` for odd prime `p >= 5` (returns `2` when `p == 3`).
#[inline]
pub const fn lls_nonresidue_bound<const LIMBS: usize>(p: &Uint<LIMBS>) -> u64 {
    if let Some(v) = p.as_u64() {
        if v <= 3 {
            return 2;
        }
    }
    let (k, m) = p.log2_mantissa4();
    let b = lls_bound_from_km(k, m);
    if b < 2 {
        2
    } else {
        b
    }
}

/// Lamzouri, Li, and Soundararajan (2015, Corollary 1.2) explicit upper bound
/// `(phi(q) * ln(q))^2` on the smallest prime `p == a (mod q)` for `q > 3` and `gcd(a, q) == 1`.
pub fn progression_prime_bound(q: u64, phi_q: u64) -> Option<u128> {
    if q <= 3 {
        return Some(7);
    }
    let q_uint = Uint::<1>::from_u64(q);
    let (k, m) = q_uint.log2_mantissa4();
    let ln_hi = ln_upper_scaled(k, m);
    let prod = (phi_q as u128).checked_mul(ln_hi)?;
    // Ceiling of (phi(q) * ln_hi / 10^10)^2: split by quotient and remainder to avoid u128 overflow.
    let quot = prod / LOG_SCALE;
    let rem = prod % LOG_SCALE;
    let q2 = quot.checked_mul(quot)?;
    let cross = quot
        .checked_mul(2)?
        .checked_mul(rem)?
        .checked_add(LOG_SCALE - 1)?
        / LOG_SCALE;
    let r2 = (rem * rem).div_ceil(LOG_SCALE_SQ);
    q2.checked_add(cross)?.checked_add(r2)
}

/// Carneiro, Milinovich, and Soundararajan (2019, Theorem 5) prime-gap step bound
/// `p_{next} - x <= (22/25) * sqrt(x) * ln(x)`, which assumes the Riemann Hypothesis, for
/// `4 <= x < 2^64`. Returns an upper bound on the number of odd candidates `(x_odd + 2*j)`
/// needed to reach the next prime. Nothing in this crate calls it; it is a helper for
/// choosing a `max_odd_steps` for [`crate::next_prime_bounded`].
pub fn rh_next_prime_step_budget_u64(x: u64) -> u64 {
    if x < 4 {
        return 2;
    }
    let x_uint = Uint::<1>::from_u64(x);
    let (k, m) = x_uint.log2_mantissa4();
    let ln_hi = ln_upper_scaled(k, m);
    let sqrt_hi = isqrt_ceil_u64(x) as u128;
    // gap <= ceil(22 * sqrt_hi * ln_hi / (25 * 10^10))
    let denom = 25u128 * LOG_SCALE;
    let gap = (22u128 * sqrt_hi * ln_hi).div_ceil(denom);
    ((gap / 2) + 2) as u64
}

/// Helper ceiling integer square root on `u64`.
#[inline]
const fn isqrt_ceil_u64(x: u64) -> u64 {
    if x <= 1 {
        return x;
    }
    let mut r = 1u64 << ((65 - x.leading_zeros()) / 2);
    loop {
        let next = (r + x / r) / 2;
        if next >= r {
            break;
        }
        r = next;
    }
    if (r as u128) * (r as u128) < (x as u128) {
        r + 1
    } else {
        r
    }
}
