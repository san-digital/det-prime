use det_prime::{
    hash_to_prime_256, hash_to_prime_be_32, is_prime, is_prime_be_32, is_prime_u64,
    least_nonresidue, prime_in_progression_u64, sqrt_mod_prime, sqrt_mod_prime_be_32,
    verify_miller_bach, MontCtx, U1024, U128, U256, U384,
};

#[test]
fn verifies_standard_cryptographic_and_zk_primes() {
    // Curve25519: 2^255 - 19
    let p25519 =
        U256::from_hex("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed").unwrap();
    assert!(is_prime(&p25519));
    let cert = verify_miller_bach(&p25519).unwrap();
    assert!(cert.prime_base_bound >= 62_000 && cert.bases_tested > 6_000);

    // secp256k1 field prime: 2^256 - 2^32 - 977 (full 256-bit top limb bit set)
    let secp =
        U256::from_hex("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f").unwrap();
    assert_eq!(secp.bits(), 256);
    assert!(is_prime(&secp));

    // NIST P-256 field prime
    let p256 =
        U256::from_hex("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff").unwrap();
    assert!(is_prime(&p256));

    // BLS12-381 scalar field r (2^32 divides r - 1)
    let bls_r =
        U256::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001").unwrap();
    assert!(is_prime(&bls_r));

    // Stark252 field prime: 2^251 + 17 * 2^192 + 1 (2^192 divides p - 1)
    let stark =
        U256::from_hex("0800000000000011000000000000000000000000000000000000000000000001").unwrap();
    assert!(is_prime(&stark));

    // Mersenne prime M_127 = 2^127 - 1
    let m127 = U128::from_hex("7fffffffffffffffffffffffffffffff").unwrap();
    assert!(is_prime(&m127));

    // NIST P-384 field prime
    let p384 = U384::from_hex(
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff",
    )
    .unwrap();
    assert!(is_prime(&p384));

    // Mersenne prime M_521 = 2^521 - 1
    let mut m521_bytes = [0xffu8; 66];
    m521_bytes[0] = 0x01;
    let m521 = U1024::from_be_bytes(&m521_bytes).unwrap();
    assert_eq!(m521.bits(), 521);
    assert!(is_prime(&m521));
}

#[test]
fn tonelli_shanks_handles_high_two_adicity_zk_fields() {
    // Stark252 has 2-adicity 192: exercises deep Tonelli-Shanks loop without randomness.
    let stark =
        U256::from_hex("0800000000000011000000000000000000000000000000000000000000000001").unwrap();
    let z = least_nonresidue(&stark).unwrap();
    assert_eq!(z, 3); // 3 is the canonical generator / non-residue of Stark252.
    assert_eq!(sqrt_mod_prime(&U256::from_u64(z), &stark).unwrap(), None);

    let ctx = MontCtx::new(stark).unwrap();
    for sample in [2u64, 4, 9, 123_456_789, 9_999_999_999_999] {
        let s_uint = U256::from_u64(sample);
        let sq = ctx.from_mont(&ctx.sqr(&ctx.to_mont(&s_uint)));
        let root = sqrt_mod_prime(&sq, &stark).unwrap().unwrap();
        let check = ctx.from_mont(&ctx.sqr(&ctx.to_mont(&root)));
        assert_eq!(check, sq);
        // Canonical root satisfies 2 * root < p.
        assert!(root <= stark.shr(1));
    }

    // Goldilocks prime p = 2^64 - 2^32 + 1 (2-adicity 32).
    let goldilocks = U128::from_u64(0xffff_ffff_0000_0001);
    let gz = least_nonresidue(&goldilocks).unwrap();
    assert_eq!(gz, 7);
    assert_eq!(
        sqrt_mod_prime(&U128::from_u64(gz), &goldilocks).unwrap(),
        None
    );

    let gctx = MontCtx::new(goldilocks).unwrap();
    let target = gctx.from_mont(&gctx.sqr(&gctx.u64_to_mont(0x1234_5678_9abc_def0)));
    let groot = sqrt_mod_prime(&target, &goldilocks).unwrap().unwrap();
    assert_eq!(gctx.from_mont(&gctx.sqr(&gctx.to_mont(&groot))), target);

    // BLS12-381 scalar field r (2-adicity 32).
    let bls_r =
        U256::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001").unwrap();
    let bz = least_nonresidue(&bls_r).unwrap();
    assert_eq!(bz, 5);
    let bctx = MontCtx::new(bls_r).unwrap();
    let bval = U256::from_hex("123456789abcdef0123456789abcdef0123456789abcdef0").unwrap();
    let bsq = bctx.from_mont(&bctx.sqr(&bctx.to_mont(&bval)));
    let broot = sqrt_mod_prime(&bsq, &bls_r).unwrap().unwrap();
    assert_eq!(bctx.from_mont(&bctx.sqr(&bctx.to_mont(&broot))), bsq);

    // secp256k1 (p == 3 mod 4 fast branch, full 256-bit modulus).
    let secp =
        U256::from_hex("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f").unwrap();
    let sctx = MontCtx::new(secp).unwrap();
    let sval =
        U256::from_hex("deadbeefcafebabe0123456789abcdefdeadbeefcafebabe0123456789abcdef").unwrap();
    let ssq = sctx.from_mont(&sctx.sqr(&sctx.to_mont(&sval)));
    let sroot = sqrt_mod_prime(&ssq, &secp).unwrap().unwrap();
    assert_eq!(sctx.from_mont(&sctx.sqr(&sctx.to_mont(&sroot))), ssq);
}

#[test]
fn deterministic_hash_to_prime_and_byte_apis_roundtrip() {
    let digest = [0x42u8; 32];
    let (p1, steps1) = hash_to_prime_256(&digest).unwrap();
    let (p2, steps2) = hash_to_prime_256(&digest).unwrap();
    assert_eq!(p1, p2);
    assert_eq!(steps1, steps2);
    assert_eq!(p1.bits(), 255);
    assert!(is_prime(&p1));

    let mut out_bytes = [0u8; 32];
    let steps3 = hash_to_prime_be_32(&digest, &mut out_bytes).unwrap();
    assert_eq!(steps3, steps1);
    assert!(is_prime_be_32(&out_bytes));

    // Square root roundtrip through 32-byte big-endian API.
    let mut a_bytes = [0u8; 32];
    a_bytes[31] = 9;
    let mut root_bytes = [0u8; 32];
    assert!(sqrt_mod_prime_be_32(&a_bytes, &out_bytes, &mut root_bytes).unwrap());
    assert_eq!(root_bytes[..31], [0u8; 31]);
    assert_eq!(root_bytes[31], 3);
}

#[test]
fn primes_in_arithmetic_progressions_within_lls_bound() {
    for q in 4u64..120 {
        for a in 1..q {
            if det_prime::Uint::<1>::from_u64(a)
                .gcd(&det_prime::Uint::<1>::from_u64(q))
                .0[0]
                != 1
            {
                continue;
            }
            let (p, steps) = prime_in_progression_u64(q, a).unwrap();
            assert!(steps >= 1);
            assert!(is_prime_u64(p));
            assert_eq!(p % q, a);
        }
    }
}
