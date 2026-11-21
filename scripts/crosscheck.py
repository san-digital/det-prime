#!/usr/bin/env python3
"""Independent reference cross-check for det-prime bounds, witnesses, and field arithmetic."""

from __future__ import annotations

import math
import sys

LN2_SCALED_HI = 6_931_471_808
LOG_SCALE = 10_000_000_000
LOG_SCALE_SQ = LOG_SCALE * LOG_SCALE


def log2_mantissa4(n: int) -> tuple[int, int]:
    if n <= 1:
        return (0, 0)
    k = n.bit_length() - 1
    if k <= 4:
        shifted = n << (4 - k)
    else:
        shifted = n >> (k - 4)
    return (k, shifted & 0xF)


def ln_upper_scaled(k: int, m: int) -> int:
    mc = min(m, 15)
    frac_left = 625_000_000 * (mc + 1)
    frac_right = LN2_SCALED_HI - 312_500_000 * (15 - mc)
    return LN2_SCALED_HI * k + min(frac_left, frac_right)


def bach_bound(n: int) -> int:
    if n <= 2:
        return 2
    k, m = log2_mantissa4(n)
    ln_hi = ln_upper_scaled(k, m)
    return max(2, (2 * ln_hi * ln_hi) // LOG_SCALE_SQ)


def lls_bound(n: int) -> int:
    if n <= 3:
        return 2
    k, m = log2_mantissa4(n)
    ln_hi = ln_upper_scaled(k, m)
    return max(2, (ln_hi * ln_hi) // LOG_SCALE_SQ)


def primes_up_to(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0] = sieve[1] = 0
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * ((limit - p * p) // p + 1)
    return [i for i, v in enumerate(sieve) if v]


def first_strong_prime_witness(n: int, prime_table: list[int]) -> int | None:
    d = n - 1
    s = 0
    while (d & 1) == 0:
        d >>= 1
        s += 1
    limit = bach_bound(n)
    for p in prime_table:
        if p > limit:
            break
        if p >= n:
            break
        if n % p == 0:
            return p
        x = pow(p, d, n)
        if x == 1 or x == n - 1:
            continue
        passed = False
        for _ in range(1, s):
            x = (x * x) % n
            if x == n - 1:
                passed = True
                break
            if x == 1:
                break
        if not passed:
            return p
    return None


def verify_log_bounds() -> None:
    for bits in [2, 3, 4, 8, 16, 32, 64, 127, 128, 251, 255, 256, 384, 521, 1024, 2048, 4096]:
        for cand in [1 << (bits - 1), (1 << bits) - 1, (1 << (bits - 1)) + ((1 << (bits - 1)) // 3)]:
            if cand < 2:
                continue
            k, m = log2_mantissa4(cand)
            assert 16 * cand < (1 << k) * (17 + m)
            ln_hi = ln_upper_scaled(k, m) / LOG_SCALE
            ln_true = math.log(cand)
            assert ln_hi > ln_true, f"ln_hi={ln_hi} <= ln_true={ln_true} at bits={bits}"
            assert bach_bound(cand) >= math.floor(2.0 * ln_true * ln_true)
            assert lls_bound(cand) >= math.floor(ln_true * ln_true)

    assert bach_bound((1 << 256) - 1) == 62_973


def verify_adversarial_composites(prime_table: list[int]) -> None:
    vectors = [
        (1195068768795265792518361315725116351898245581, 37),
        (318665857834031151167461, 41),
        (3317044064679887385961981, 43),
        (3825123056546413051, 37),
        (2289833795952786091229564300348384801661184049187983124796226138314273151449, 2),
        (((1 << 127) - 1) ** 2, 2),
    ]
    for comp, expected_witness in vectors:
        got = first_strong_prime_witness(comp, prime_table)
        assert got == expected_witness, f"expected witness {expected_witness}, got {got}"

    # Verify Chernick Carmichael passes Fermat test for coprime primes up to 97.
    carm = vectors[4][0]
    for p in prime_table[:25]:
        if math.gcd(p, carm) == 1:
            assert pow(p, carm - 1, carm) == 1


def verify_zk_nonresidues(prime_table: list[int]) -> None:
    fields = [
        ("Stark252", (1 << 251) + 17 * (1 << 192) + 1, 3),
        ("Goldilocks", (1 << 64) - (1 << 32) + 1, 7),
        (
            "BLS12-381-r",
            0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001,
            5,
        ),
    ]
    for name, p, expected_z in fields:
        bound = lls_bound(p)
        found = None
        for q in prime_table:
            if q > bound:
                break
            if pow(q, (p - 1) // 2, p) == p - 1:
                found = q
                break
        assert found == expected_z, f"{name}: expected {expected_z}, got {found}"


def main() -> int:
    prime_table = primes_up_to(100_000)
    assert len(primes_up_to(1_000_000)) == 78_498
    verify_log_bounds()
    verify_adversarial_composites(prime_table)
    verify_zk_nonresidues(prime_table)
    print("crosscheck: ok (log bounds, pseudoprime witnesses, Carmichael Fermat check, ZK non-residues)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
