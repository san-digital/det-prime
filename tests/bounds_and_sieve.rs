use det_prime::{
    bach_witness_bound, is_prime_u64, lls_nonresidue_bound, verify_miller_bach, PrimeIter, Uint,
    MAX_SIEVE_LIMIT, U256, U4096,
};

#[test]
fn segmented_sieve_matches_exact_prime_counts() {
    let c_100 = PrimeIter::up_to(100).count();
    assert_eq!(c_100, 25);

    let c_1m = PrimeIter::up_to(1_000_000).count();
    assert_eq!(c_1m, 78_498);

    let c_max = PrimeIter::up_to(MAX_SIEVE_LIMIT).count();
    assert_eq!(c_max, 1_061_198);
}

#[test]
fn primality_matches_trial_division_up_to_50_000() {
    for n in 0u64..=50_000 {
        let mut expected = n >= 2;
        if expected {
            let mut d = 2u64;
            while d * d <= n {
                if n % d == 0 {
                    expected = false;
                    break;
                }
                d += 1;
            }
        }
        assert_eq!(is_prime_u64(n), expected, "mismatch on is_prime_u64({n})");
        let u = Uint::<1>::from_u64(n);
        assert_eq!(
            verify_miller_bach(&u).is_ok(),
            expected,
            "mismatch on verify_miller_bach({n})"
        );
    }
}

#[test]
fn integer_log_bounds_enclose_true_logarithms_tightly() {
    for bits in [2u32, 3, 8, 16, 64, 128, 255, 256, 512, 1024, 2048, 4096] {
        // Test 2^(bits - 1) and 2^bits - 1.
        let mut low_limbs = [0u64; 64];
        let k = bits - 1;
        low_limbs[(k / 64) as usize] = 1u64 << (k % 64);
        let n_low = U4096::from_limbs(low_limbs);

        let ln_exact_low = (k as f64) * core::f64::consts::LN_2;
        let two_ln_sq_low = 2.0 * ln_exact_low * ln_exact_low;
        let b_low = bach_witness_bound(&n_low) as f64;
        assert!(
            b_low + 1.0 > two_ln_sq_low,
            "bound {b_low} below 2*(ln n)^2 = {two_ln_sq_low} at bits={bits}"
        );
        if bits >= 64 {
            assert!(
                b_low < two_ln_sq_low * 1.02 + 2.0,
                "bound {b_low} looser than 2% at bits={bits}"
            );
        }

        let lls_low = lls_nonresidue_bound(&n_low) as f64;
        assert!(lls_low + 1.0 > ln_exact_low * ln_exact_low);
    }

    // Spot-check 256-bit max (2^256 - 1): 2 * (256 * ln 2)^2 = 62973.937..., floor is 62973.
    let max256 = U256::from_limbs([u64::MAX; 4]);
    let b256 = bach_witness_bound(&max256);
    assert_eq!(b256, 62_973);

    // Degenerate zero-modulus / zero-limb public API guards never panic.
    assert_eq!(det_prime::jacobi_u64(5, 0), 0);
    assert_eq!(det_prime::jacobi_u64(5, 1), 1);
    assert_eq!(det_prime::jacobi_u64(5, 4), 0);
    assert_eq!(det_prime::jacobi_prime_mod_odd(0, &max256), 0);
    assert_eq!(det_prime::jacobi_prime_mod_odd(3, &Uint::<0>::ZERO), 0);
    assert_eq!(
        det_prime::next_prime_bounded(&Uint::<0>::ZERO, 5),
        Err(det_prime::Error::Overflow)
    );
}
