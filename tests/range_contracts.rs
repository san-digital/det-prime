use det_prime::{
    euler_totient_u64, hash_to_prime_256, hash_to_prime_be_32, is_prime, is_prime_u64,
    next_prime_bounded, prime_in_progression_u64, progression_prime_bound, Error, U256,
};

const LOW: U256 = U256::from_limbs([1, 0, 0, 1 << 62]); // 2^254 + 1
const HIGH: U256 = U256::from_limbs([u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1]); // 2^255 - 1

fn start_of(digest: &[u8; 32]) -> U256 {
    let mut buf = *digest;
    buf[0] = (buf[0] & 0x7f) | 0x40;
    buf[31] |= 0x01;
    U256::from_be_bytes(&buf).unwrap()
}

#[test]
fn hash_to_prime_stays_below_2_pow_255_for_top_of_range_digests() {
    // The largest prime below 2^255 is 2^255 - 19, so every start above it (trailing bytes
    // 0xee..=0xff after an all-0xff prefix) used to step past 2^255 and return a 256-bit
    // prime (2^255 + 95 for an all-0xff digest).
    for last in 0xe0u8..=0xff {
        let mut digest = [0xffu8; 32];
        digest[31] = last;
        let (p, steps) = hash_to_prime_256(&digest).unwrap();
        assert_eq!(p.bits(), 255, "digest ..{last:02x} mapped to {p:?}");
        assert!(LOW <= p && p <= HIGH);
        assert!(is_prime(&p));
        assert!(steps >= 1);
    }

    // Starts above 2^255 - 19 wrap to the bottom of the range: 2^255 - 1 is composite, so the
    // all-0xff digest lands on the smallest prime above 2^254.
    let (p, _) = hash_to_prime_256(&[0xff; 32]).unwrap();
    assert_eq!(p, next_prime_bounded(&LOW, 16_384).unwrap().0);

    let mut out = [0u8; 32];
    hash_to_prime_be_32(&[0xff; 32], &mut out).unwrap();
    assert_eq!(out[0] & 0xc0, 0x40, "bit 255 must be clear and bit 254 set");
}

#[test]
fn hash_to_prime_is_unchanged_wherever_no_wrap_is_needed() {
    let (p, steps) = hash_to_prime_256(&[0x42; 32]).unwrap();
    assert_eq!(
        p,
        U256::from_hex("4242424242424242424242424242424242424242424242424242424242424319").unwrap()
    );
    assert_eq!(steps, 108);

    let mut digest = [0xffu8; 32];
    digest[31] = 0x00; // start 2^255 - 255, below the last prime 2^255 - 19
    let (p, steps) = hash_to_prime_256(&digest).unwrap();
    assert_eq!(p, HIGH.wrapping_sub(&U256::from_u64(30))); // 2^255 - 31
    assert_eq!(
        (p, steps),
        next_prime_bounded(&start_of(&digest), 16_384).unwrap()
    );

    for seed in 0u8..16 {
        let digest = [seed.wrapping_mul(37).wrapping_add(11); 32];
        assert_eq!(
            hash_to_prime_256(&digest).unwrap(),
            next_prime_bounded(&start_of(&digest), 16_384).unwrap()
        );
    }
}

#[test]
fn prime_in_progression_handles_moduli_whose_bound_overflows_u128() {
    // (phi(q) * ln q)^2 does not fit in u128 for q near 2^60, which used to surface as
    // Err(Overflow) even though the scan is capped at u64::MAX anyway.
    let q = (1u64 << 60) + 1;
    assert!(progression_prime_bound(q, euler_totient_u64(q)).is_none());
    let (p, steps) = prime_in_progression_u64(q, 1).unwrap();
    assert_eq!(p, 14 * q + 1);
    assert_eq!(steps, 15);
    assert!(is_prime_u64(p));

    // When no member of the progression below u64::MAX is prime, the answer is a step-budget
    // miss, not an arithmetic overflow.
    for q in [(1u64 << 62) + 1, u64::MAX - 1, u64::MAX] {
        assert_eq!(
            prime_in_progression_u64(q, 1),
            Err(Error::StepBudgetExceeded)
        );
    }
}
